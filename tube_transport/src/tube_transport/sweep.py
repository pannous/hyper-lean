"""Run experiments A--E and write traceable CSV/plots/summary."""

from __future__ import annotations

import argparse
from dataclasses import asdict
import csv
import json
import math
from pathlib import Path
from typing import Any, Iterable

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

from .acoustics import simulate_periodic_line
from .model import (
    ATM_PA,
    Air,
    FlowPath,
    Geometry,
    compliant_station,
    evaluate_flow,
    pump_power,
    required_effective_area_for_pressure_limit,
)


def _write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fields: list[str] = []
    seen: set[str] = set()
    for row in rows:
        for key in row:
            if key not in seen:
                seen.add(key)
                fields.append(key)
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(rows)


def _flow_row(experiment: str, geometry: Geometry, speed: float, pressure_atm: float,
              shape: str, result: Any, **extra: Any) -> dict[str, Any]:
    row = {
        "experiment": experiment,
        "pod_diameter_m": geometry.pod_diameter_m,
        "tube_diameter_m": geometry.tube_diameter_m,
        "blockage_ratio": geometry.blockage,
        "speed_m_s": speed,
        "pressure_atm": pressure_atm,
        "shape": shape,
    }
    row.update(asdict(result))
    row["flags"] = ";".join(result.flags)
    row.update(extra)
    return row


def run(config: dict[str, Any], output: Path) -> dict[str, list[dict[str, Any]]]:
    output.mkdir(parents=True, exist_ok=True)
    air = Air(temperature_k=float(config["temperature_K"]))
    pod_d = float(config["pod_diameter_m"])
    pod_l = float(config["pod_length_m"])
    cds = config["discharge_coefficients"]
    tol = float(config["pressure_difference_target_fraction"])

    rows_a: list[dict[str, Any]] = []
    rows_b: list[dict[str, Any]] = []
    rows_c: list[dict[str, Any]] = []
    rows_d: list[dict[str, Any]] = []
    rows_e: list[dict[str, Any]] = []

    for tube_d in config["tube_diameters_m"]:
        geometry = Geometry(pod_d, float(tube_d), pod_l)
        annulus = FlowPath("annulus", geometry.annulus_area_m2, float(cds["annulus"]))
        for speed in config["speeds_m_s"]:
            for pressure_atm in config["pressures_atm"]:
                pressure = float(pressure_atm) * ATM_PA
                for shape in config["shapes"]:
                    result = evaluate_flow(geometry, float(speed), pressure, [annulus], air, shape)
                    rows_a.append(_flow_row("A", geometry, speed, pressure_atm, shape, result))

                rho = air.density(pressure)
                mdot = rho * geometry.pod_area_m2 * float(speed)
                required_eff = required_effective_area_for_pressure_limit(mdot, pressure, tol, air)
                required_bypass = max(
                    0.0,
                    (required_eff - annulus.effective_area_m2) / float(cds["dedicated_bypass"]),
                )
                for bypass_area in config["bypass_areas_m2"]:
                    bypass = FlowPath("dedicated_bypass", float(bypass_area), float(cds["dedicated_bypass"]))
                    result = evaluate_flow(geometry, float(speed), pressure, [annulus, bypass], air, "piston")
                    rows_b.append(_flow_row(
                        "B", geometry, speed, pressure_atm, "piston", result,
                        bypass_area_m2=bypass_area,
                        required_bypass_area_for_target_m2=required_bypass,
                        target_relative_pressure_difference=tol,
                    ))

        # C uses a representative pressure because ideal pressure ratios do not
        # depend on absolute pressure.  Reynolds and absolute energy still do.
        pressure_atm = 0.01
        pressure = pressure_atm * ATM_PA
        for speed in config["speeds_m_s"]:
            open_result = evaluate_flow(geometry, float(speed), pressure, [annulus], air, "piston")
            rows_c.append(_flow_row(
                "C", geometry, speed, pressure_atm, "piston", open_result,
                architecture="open_annulus", duct_area_fraction=1.0,
                return_area_m2=geometry.annulus_area_m2,
            ))
            for fraction in config["integrated_duct_area_fractions"]:
                area = geometry.annulus_area_m2 * float(fraction)
                duct = FlowPath("integrated_duct", area, float(cds["integrated_duct"]))
                result = evaluate_flow(geometry, float(speed), pressure, [duct], air, "piston")
                rows_c.append(_flow_row(
                    "C", geometry, speed, pressure_atm, "piston", result,
                    architecture="partitioned_integrated_ducts",
                    duct_area_fraction=fraction,
                    return_area_m2=area,
                ))

    # D focuses on the central 2.0 m pressure vessel question.
    geometry = Geometry(pod_d, 2.0, pod_l)
    pump_cfg = config["pump"]
    for speed in config["speeds_m_s"]:
        for pressure_atm in config["pressures_atm"]:
            pressure = float(pressure_atm) * ATM_PA
            onboard = pump_power(
                geometry, float(speed), pressure,
                float(pump_cfg["onboard_flow_area_m2"]),
                float(pump_cfg["return_path_loss_coefficient"]),
                float(pump_cfg["onboard_efficiency"]), air,
            )
            for area in [a for a in config["bypass_areas_m2"] if a > 0]:
                stationary = pump_power(
                    geometry, float(speed), pressure, float(area),
                    float(pump_cfg["return_path_loss_coefficient"]),
                    float(pump_cfg["stationary_efficiency"]), air,
                )
                row = {
                    "experiment": "D",
                    "pod_diameter_m": pod_d,
                    "tube_diameter_m": 2.0,
                    "blockage_ratio": geometry.blockage,
                    "speed_m_s": speed,
                    "pressure_atm": pressure_atm,
                    "stationary_bypass_area_m2": area,
                    **{f"stationary_{k}": v for k, v in stationary.items()},
                    **{f"onboard_{k}": v for k, v in onboard.items()},
                }
                row["stationary_to_onboard_power_ratio"] = (
                    float(stationary["shaft_power_w"]) / float(onboard["shaft_power_w"])
                )
                rows_d.append(row)

    # E: capacity and transmission-line implications.
    geometry = Geometry(pod_d, 2.0, pod_l)
    for pressure_atm in config["pressures_atm"]:
        pressure = float(pressure_atm) * ATM_PA
        for spacing in config["chamber_spacings_m"]:
            for fraction in config["chamber_pressure_fractions"]:
                values = compliant_station(
                    geometry, float(spacing), pressure, float(fraction),
                    float(config["loss_fraction_per_chamber_cycle"]), air,
                )
                rows_e.append({
                    "experiment": "E",
                    "pod_diameter_m": pod_d,
                    "tube_diameter_m": 2.0,
                    "blockage_ratio": geometry.blockage,
                    "pressure_atm": pressure_atm,
                    "station_spacing_m": spacing,
                    "target_pressure_fraction": fraction,
                    **values,
                    "flags": "large_swept_volume" if values["swept_volume_per_station_m3"] > 20 else "",
                })

    cost_rows = _cost_screening(config, rows_a, rows_b, air)
    datasets = {"A": rows_a, "B": rows_b, "C": rows_c, "D": rows_d, "E": rows_e, "cost": cost_rows}
    for name, rows in datasets.items():
        filename = "cost_proxy.csv" if name == "cost" else f"experiment_{name}.csv"
        _write_csv(output / filename, rows)

    acoustic_summary = _run_acoustics(config, output, air)
    _make_plots(datasets, output)
    _write_summary(config, datasets, acoustic_summary, output)
    return datasets


def _cost_screening(config: dict[str, Any], rows_a: list[dict[str, Any]],
                    rows_b: list[dict[str, Any]], air: Air) -> list[dict[str, Any]]:
    """Dimensionless lifecycle-cost sensitivity, not a monetary estimate."""
    proxy = config["cost_proxy"]
    d_ref = float(proxy["diameter_reference_m"])
    a_ref = float(proxy["bypass_area_reference_m2"])
    pod_d = float(config["pod_diameter_m"])
    pod_l = float(config["pod_length_m"])
    cds = config["discharge_coefficients"]

    reference_energy: dict[tuple[float, float], float] = {}
    for row in rows_a:
        if row["tube_diameter_m"] == d_ref and row["shape"] == "piston":
            reference_energy[(float(row["speed_m_s"]), float(row["pressure_atm"]))] = float(
                row["energy_kwh_per_vehicle_km"]
            )

    required: dict[tuple[float, float, float], float] = {}
    for row in rows_b:
        key = (float(row["tube_diameter_m"]), float(row["speed_m_s"]), float(row["pressure_atm"]))
        required[key] = float(row["required_bypass_area_for_target_m2"])

    output: list[dict[str, Any]] = []
    baseline_rows = [row for row in rows_a if row["shape"] == "piston"]
    for baseline in baseline_rows:
        tube_d = float(baseline["tube_diameter_m"])
        speed = float(baseline["speed_m_s"])
        pressure_atm = float(baseline["pressure_atm"])
        geometry = Geometry(pod_d, tube_d, pod_l)
        bypass_area = required[(tube_d, speed, pressure_atm)]
        annulus = FlowPath("annulus", geometry.annulus_area_m2, float(cds["annulus"]))
        bypass = FlowPath("dedicated_bypass", bypass_area, float(cds["dedicated_bypass"]))
        managed = evaluate_flow(
            geometry, speed, pressure_atm * ATM_PA, [annulus, bypass], air, "piston"
        )
        architectures = [
            ("ordinary_annulus", 0.0, float(baseline["energy_kwh_per_vehicle_km"]), float(baseline["pressure_ratio"])),
            ("bypass_at_5pct_target", bypass_area, managed.energy_kwh_per_vehicle_km, managed.pressure_ratio),
        ]
        for architecture, area, energy, pressure_ratio in architectures:
            terms = {
                "structure": (tube_d / d_ref) ** 2,
                "vacuum": (tube_d / d_ref) ** 2,
                "bypass": area / a_ref,
                "propulsion": energy / reference_energy[(speed, pressure_atm)],
                "maintenance": 0.7 * tube_d / d_ref + 0.3 * area / a_ref,
            }
            for scenario, weights in proxy["scenarios"].items():
                if abs(sum(float(value) for value in weights.values()) - 1.0) > 1e-12:
                    raise ValueError(f"cost weights for {scenario} do not sum to one")
                total = sum(float(weights[name]) * terms[name] for name in terms)
                output.append({
                    "architecture": architecture,
                    "scenario": scenario,
                    "pod_diameter_m": pod_d,
                    "tube_diameter_m": tube_d,
                    "blockage_ratio": geometry.blockage,
                    "speed_m_s": speed,
                    "pressure_atm": pressure_atm,
                    "bypass_area_m2": area,
                    "pressure_ratio": pressure_ratio,
                    "energy_kwh_per_vehicle_km": energy,
                    **{f"term_{name}": value for name, value in terms.items()},
                    **{f"weight_{name}": float(weights[name]) for name in terms},
                    "total_cost_proxy": total,
                    "warning": "dimensionless_sensitivity_not_monetary_cost",
                })
    return output


def _run_acoustics(config: dict[str, Any], output: Path, air: Air) -> list[dict[str, Any]]:
    geometry = Geometry(float(config["pod_diameter_m"]), 2.0, float(config["pod_length_m"]))
    pressure = 0.01 * ATM_PA
    speed = 200.0
    station = compliant_station(geometry, 10.0, pressure, 0.05, 0.1, air)
    added_c_per_m = station["required_compliance_m3_pa"] / 10.0
    cases = {
        "baseline": simulate_periodic_line(geometry, speed, pressure, air=air),
        "compliant_5pct": simulate_periodic_line(
            geometry, speed, pressure, added_compliance_per_m_m3_pa=added_c_per_m, air=air
        ),
    }
    rows: list[dict[str, Any]] = []
    fig, ax = plt.subplots(figsize=(7.2, 4.4))
    for name, result in cases.items():
        ax.plot(result.time_s, result.peak_pressure_pa, label=name)
        rows.append({
            "case": name,
            "peak_pressure_pa": float(np.max(result.peak_pressure_pa)),
            "effective_wave_speed_m_s": result.effective_wave_speed_m_s,
            "mass_balance_equivalent_m3": result.mass_balance_equivalent_m3,
            "dx_m": result.dx_m,
            "dt_s": result.dt_s,
        })
    ax.axhline(0.05 * pressure, color="black", linestyle="--", linewidth=1, label="5% pressure target")
    ax.set(xlabel="time (s)", ylabel="peak |gauge pressure| (Pa)", title="1-D periodic acoustic line: 2.0 m tube, 200 m/s")
    ax.grid(True, alpha=0.3)
    ax.legend()
    fig.tight_layout()
    fig.savefig(output / "acoustic_response.png", dpi=160)
    plt.close(fig)
    _write_csv(output / "acoustic_summary.csv", rows)
    return rows


def _make_plots(data: dict[str, list[dict[str, Any]]], output: Path) -> None:
    # Exact blockage geometry.
    a = data["A"]
    representative = {
        row["tube_diameter_m"]: row["blockage_ratio"]
        for row in a if row["speed_m_s"] == 50 and row["pressure_atm"] == 0.001 and row["shape"] == "piston"
    }
    fig, ax = plt.subplots(figsize=(6.8, 4.2))
    ax.plot(list(representative), list(representative.values()), "o-")
    ax.set(xlabel="tube diameter (m)", ylabel="blockage ratio beta", title="1.5 m pod geometric blockage")
    ax.grid(True, alpha=0.3)
    fig.tight_layout()
    fig.savefig(output / "blockage_vs_tube.png", dpi=160)
    plt.close(fig)

    # Experiment A pressure-ratio curves at 0.01 atm.
    fig, ax = plt.subplots(figsize=(7.2, 4.5))
    for tube in sorted(representative):
        rows = [r for r in a if r["tube_diameter_m"] == tube and r["pressure_atm"] == 0.01 and r["shape"] == "piston"]
        ax.plot([r["speed_m_s"] for r in rows], [r["pressure_ratio"] for r in rows], "o-", label=f"D={tube:g} m")
    ax.set(xlabel="pod speed (m/s)", ylabel="front / rear pressure", title="Experiment A: ordinary annular return")
    ax.grid(True, alpha=0.3)
    ax.legend(ncol=2)
    fig.tight_layout()
    fig.savefig(output / "ordinary_annulus_pressure_ratio.png", dpi=160)
    plt.close(fig)

    # Experiment B required bypass for the 2 m vessel.
    b = data["B"]
    picked: dict[float, float] = {}
    for row in b:
        if row["tube_diameter_m"] == 2.0 and row["pressure_atm"] == 0.01 and row["bypass_area_m2"] == 0.0:
            picked[row["speed_m_s"]] = row["required_bypass_area_for_target_m2"]
    fig, ax = plt.subplots(figsize=(6.8, 4.2))
    ax.plot(list(picked), list(picked.values()), "o-")
    ax.set(xlabel="pod speed (m/s)", ylabel="additional bypass area (m^2)",
           title="Experiment B: area for delta-p <= 5% (2.0 m tube)")
    ax.grid(True, alpha=0.3)
    fig.tight_layout()
    fig.savefig(output / "required_bypass_area_2m.png", dpi=160)
    plt.close(fig)

    # D power-area tradeoff at 200 m/s, 0.01 atm.
    d = [r for r in data["D"] if r["speed_m_s"] == 200 and r["pressure_atm"] == 0.01]
    fig, ax = plt.subplots(figsize=(6.8, 4.2))
    ax.loglog([r["stationary_bypass_area_m2"] for r in d], [r["stationary_shaft_power_w"] / 1000 for r in d], "o-")
    ax.set(xlabel="stationary return area (m^2)", ylabel="shaft power (kW)",
           title="Experiment D: idealized pumping at 200 m/s, 0.01 atm")
    ax.grid(True, which="both", alpha=0.3)
    fig.tight_layout()
    fig.savefig(output / "stationary_pumping_power.png", dpi=160)
    plt.close(fig)

    # E chamber swept volume.
    e = [r for r in data["E"] if r["pressure_atm"] == 0.01 and r["target_pressure_fraction"] == 0.05]
    fig, ax = plt.subplots(figsize=(6.8, 4.2))
    ax.plot([r["station_spacing_m"] for r in e], [r["swept_volume_per_station_m3"] for r in e], "o-")
    ax.set(xlabel="station spacing (m)", ylabel="required swept volume per station (m^3)",
           title="Experiment E: local volume cannot be eliminated")
    ax.grid(True, alpha=0.3)
    fig.tight_layout()
    fig.savefig(output / "compliant_swept_volume.png", dpi=160)
    plt.close(fig)

    cost = [
        row for row in data["cost"]
        if row["speed_m_s"] == 300 and row["pressure_atm"] == 0.01
        and row["architecture"] == "bypass_at_5pct_target"
    ]
    fig, ax = plt.subplots(figsize=(7.2, 4.4))
    for scenario in sorted({row["scenario"] for row in cost}):
        rows = sorted((row for row in cost if row["scenario"] == scenario), key=lambda row: row["tube_diameter_m"])
        ax.plot([row["tube_diameter_m"] for row in rows], [row["total_cost_proxy"] for row in rows], "o-", label=scenario)
    ax.set(xlabel="tube diameter (m)", ylabel="dimensionless total-cost proxy",
           title="Sensitivity only: bypass sized for 5% delta-p at 300 m/s")
    ax.grid(True, alpha=0.3)
    ax.legend()
    fig.tight_layout()
    fig.savefig(output / "cost_proxy_tradeoff.png", dpi=160)
    plt.close(fig)

    cfd_path = output.parent / "openfoam" / "results" / "cfd_summary.csv"
    if cfd_path.exists():
        with cfd_path.open(encoding="utf-8", newline="") as handle:
            cfd = list(csv.DictReader(handle))
        reduced = {
            float(row["speed_m_s"]): row
            for row in a
            if row["tube_diameter_m"] == 2.0 and row["pressure_atm"] == 0.01 and row["shape"] == "piston"
        }
        speeds = [float(row["speed_m_s"]) for row in cfd]
        fig, axes = plt.subplots(1, 2, figsize=(10.4, 4.2))
        axes[0].plot(speeds, [float(reduced[s]["pressure_ratio"]) for s in speeds], "o--", label="reduced")
        axes[0].plot(speeds, [float(row["pressure_ratio"]) for row in cfd], "s-", label="OpenFOAM")
        axes[0].set(xlabel="speed (m/s)", ylabel="front / rear pressure", title="Pressure ratio")
        axes[0].grid(True, alpha=0.3)
        axes[0].legend()
        axes[1].plot(speeds, [float(reduced[s]["max_mach"]) for s in speeds], "o--", label="reduced path")
        axes[1].plot(speeds, [float(row["annulus_rear_mach"]) for row in cfd], "s-", label="CFD rear annulus")
        axes[1].plot(speeds, [float(row["max_mach"]) for row in cfd], "^-", label="CFD global max")
        axes[1].axhline(1.0, color="black", linewidth=1, linestyle=":")
        axes[1].set(xlabel="speed (m/s)", ylabel="Mach", title="Compressible transition")
        axes[1].grid(True, alpha=0.3)
        axes[1].legend()
        fig.suptitle("1.5 m pod in 2.0 m tube at 0.01 atm")
        fig.tight_layout()
        fig.savefig(output / "reduced_vs_openfoam.png", dpi=160)
        plt.close(fig)


def _write_summary(config: dict[str, Any], data: dict[str, list[dict[str, Any]]],
                   acoustic: list[dict[str, Any]], output: Path) -> None:
    a2 = [r for r in data["A"] if r["tube_diameter_m"] == 2.0 and r["pressure_atm"] == 0.01 and r["shape"] == "piston"]
    b2 = [r for r in data["B"] if r["tube_diameter_m"] == 2.0 and r["pressure_atm"] == 0.01 and r["bypass_area_m2"] == 0.0]
    d200 = [r for r in data["D"] if r["speed_m_s"] == 200 and r["pressure_atm"] == 0.01]
    d200.sort(key=lambda row: abs(row["stationary_path_mach"] - 0.3))
    station = next(r for r in data["E"] if r["pressure_atm"] == 0.01 and r["station_spacing_m"] == 10.0 and r["target_pressure_fraction"] == 0.05)
    lines = [
        "# Screening results: low-pressure tube gas management",
        "",
        "These are reduced-order results. Rows at or near choking are candidates for CFD, not validated designs.",
        "",
        "## Central 1.5 m pod / 2.0 m tube result",
        "",
        f"The geometric blockage ratio is **{a2[0]['blockage_ratio']:.4f}** and the free annulus is "
        f"**{math.pi * (2.0**2 - 1.5**2) / 4:.3f} m²**.",
        "",
        "| speed (m/s) | front/rear p | max Mach | Kantrowitz capacity | energy (kWh/vehicle-km) | flags |",
        "|---:|---:|---:|---:|---:|---|",
    ]
    for row in a2:
        lines.append(
            f"| {row['speed_m_s']} | {row['pressure_ratio']:.3f} | {row['max_mach']:.3f} | "
            f"{row['kantrowitz_capacity_ratio']:.3f} | {row['energy_kwh_per_vehicle_km']:.4f} | {row['flags']} |"
        )
    lines += [
        "",
        "The ideal Kantrowitz ratio is independent of absolute pressure. Lower pressure reduces mass and energy, but not the volume-flow or area requirement.",
        "",
        "## Experiment B: dedicated bypass area for 5% pressure difference",
        "",
        "| speed (m/s) | additional bypass area (m²) |",
        "|---:|---:|",
    ]
    for row in b2:
        lines.append(f"| {row['speed_m_s']} | {row['required_bypass_area_for_target_m2']:.3f} |")
    lines += [
        "",
        "This is a best-case effective-area estimate. A real long bypass with bends, friction, valves and pump stations needs more area or active pressure rise.",
        "",
        "## Experiment C: integrated ducts",
        "",
        "Partitioning exactly the same free cross-section does not create flow capacity. In this model it performs worse than an unobstructed annulus because walls and entrances lower the discharge coefficient. Integrated ducts become interesting only when they reclaim space that was not otherwise a usable flow path, or when they enable active control.",
        "",
        "## Experiment D: stationary pumping",
        "",
        f"At 200 m/s the pod displaces **{math.pi * 1.5**2 / 4 * 200:.1f} m³/s**. "
        f"Keeping a return path below Mach 0.3 needs about **{d200[0]['stationary_minimum_area_for_mach_0_3_m2']:.2f} m²**. "
        "Pump power falls strongly with pressure, but machinery still has to handle the full volume flow. Rows above Mach 0.3 should not be interpreted with the incompressible loss formula.",
        "",
        "## Experiment E: compliant local reservoirs",
        "",
        f"For 10 m station spacing, each station must sweep **{station['swept_volume_per_station_m3']:.2f} m³**. "
        f"A passive gas accumulator limited to 5% pressure change would need approximately **{station['equivalent_gas_accumulator_volume_m3']:.1f} m³** of gas volume per station. "
        f"The invariant displaced volume is **{station['swept_volume_per_vehicle_km_m3']:.1f} m³ per vehicle-km**.",
        "",
        "The ideal compliance lowers acoustic impedance and wave speed, but it stores rather than destroys the pulse. Any damping or hysteresis becomes propulsion energy loss.",
        "",
        "## Total-system cost sensitivity",
        "",
        "`cost_proxy.csv` combines normalized tube structure, vacuum volume, bypass area, propulsion energy and maintenance terms. The weight sets are disclosed in `config/default.json`; the index is deliberately dimensionless and must not be read as a monetary estimate.",
        "",
    ]
    cost_slice = [
        row for row in data["cost"]
        if row["speed_m_s"] == 300 and row["pressure_atm"] == 0.01
        and row["architecture"] == "bypass_at_5pct_target"
    ]
    lines += [
        "At 300 m/s and 0.01 atm, with bypass sized to the 5% pressure target:",
        "",
        "| weighting scenario | minimum-index tube (m) | required bypass (m²) | cost proxy |",
        "|---|---:|---:|---:|",
    ]
    for scenario in sorted({row["scenario"] for row in cost_slice}):
        rows = [row for row in cost_slice if row["scenario"] == scenario]
        best = min(rows, key=lambda row: row["total_cost_proxy"])
        lines.append(
            f"| {scenario} | {best['tube_diameter_m']:.1f} | {best['bypass_area_m2']:.3f} | {best['total_cost_proxy']:.3f} |"
        )
    lines += [
        "",
        "The winner changes only in the deliberately diameter-dominant scenario. That is the useful economic result: a small tube is not automatically cheaper once the several-square-metre return path is priced, and the decision depends on calibrated civil/structural costs rather than aerodynamics alone.",
        "",
        "## Numerical acoustic check",
        "",
        "| case | peak pressure (Pa) | wave speed (m/s) | volume-balance error (m³ equivalent) |",
        "|---|---:|---:|---:|",
    ]
    for row in acoustic:
        lines.append(
            f"| {row['case']} | {row['peak_pressure_pa']:.2f} | {row['effective_wave_speed_m_s']:.2f} | {row['mass_balance_equivalent_m3']:.3e} |"
        )
    cfd_path = output.parent / "openfoam" / "results" / "cfd_summary.csv"
    if cfd_path.exists():
        with cfd_path.open(encoding="utf-8", newline="") as handle:
            cfd_rows = list(csv.DictReader(handle))
        lines += [
            "",
            "## OpenFOAM 14 axisymmetric-wedge screening",
            "",
            "These are inviscid, abrupt-piston, early-transient snapshots before the initial wave reaches the far boundaries. They are useful for locating the compressible transition, not for final drag design.",
            "",
            "| speed (m/s) | front/rear p | annulus Mach front/mid/rear | global max Mach | choking location | pressure force (N) | force closure error | mass-flow imbalance |",
            "|---:|---:|---:|---:|---|---:|---:|---:|",
        ]
        for row in cfd_rows:
            lines.append(
                f"| {float(row['speed_m_s']):.0f} | {float(row['pressure_ratio']):.3f} | "
                f"{float(row['annulus_front_mach']):.3f} / {float(row['annulus_mid_mach']):.3f} / {float(row['annulus_rear_mach']):.3f} | "
                f"{float(row['max_mach']):.3f} | {row['choking_location']} | "
                f"{float(row['pod_pressure_force_x_n']):.1f} | {float(row['pressure_force_closure_relative_error']):.2e} | "
                f"{float(row['boundary_mass_flow_relative_imbalance']):.2e} |"
            )
        lines += [
            "",
            "At 150 m/s the sampled annulus remains subsonic but the abrupt trailing-edge wake just exceeds Mach 1. At 250 m/s the rear annulus is already supersonic. This brackets the transition and makes 200 m/s the next convergence/refinement point.",
        ]
    lines += [
        "",
        "## Decision for CFD",
        "",
        "Prioritize a refined 2.0 m-tube case at 200 m/s, then compare the open annulus against a bypass with at least the calculated effective area. Very small bypasses and small local reservoirs are already rejected by continuity.",
        "",
        "## Conservation checks",
        "",
        "- All quasi-steady rows solve mass flow to a relative residual recorded in CSV.",
        "- Pressure work `delta_p * Q` equals pressure-drag power `F * V` by construction; the residual is recorded.",
        "- The acoustic source/sink pair has zero net injected volume; its residual is shown above.",
        "- Compliance capacity is tied to `A_pod * station spacing`; no hydraulic multiplier changes that swept-volume requirement.",
    ]
    (output / "SUMMARY.md").write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--config", type=Path, default=Path("config/default.json"))
    parser.add_argument("--output", type=Path, default=Path("results"))
    args = parser.parse_args()
    config = json.loads(args.config.read_text(encoding="utf-8"))
    run(config, args.output)
    print(f"Wrote experiment A--E results to {args.output}")


if __name__ == "__main__":
    main()
