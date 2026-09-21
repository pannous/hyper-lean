#!/usr/bin/env python3
"""Extract the final OpenFOAM function-object values into one CSV."""

from __future__ import annotations

import argparse
import csv
import re
from pathlib import Path


FLOAT = r"[-+]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][-+]?\d+)?"


def last_data_row(root: Path, pattern: str) -> list[float] | None:
    files = sorted(root.glob(pattern))
    if not files:
        return None
    rows: list[list[float]] = []
    for line in files[-1].read_text(encoding="utf-8", errors="replace").splitlines():
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        values = [float(x) for x in re.findall(FLOAT, line)]
        if values:
            rows.append(values)
    return rows[-1] if rows else None


def metadata(path: Path) -> dict[str, str]:
    result: dict[str, str] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        if "=" in line:
            key, value = line.split("=", 1)
            result[key] = value
    return result


def parse_case(case: Path) -> dict[str, object]:
    meta = metadata(case / "CASE_METADATA.txt")
    post = case / "postProcessing"
    front = last_data_row(post, "frontPressure/*/surfaceFieldValue.dat")
    rear = last_data_row(post, "rearPressure/*/surfaceFieldValue.dat")
    inlet = last_data_row(post, "inletMassFlow/*/surfaceFieldValue.dat")
    outlet = last_data_row(post, "outletMassFlow/*/surfaceFieldValue.dat")
    forces = last_data_row(post, "podForces/*/forces.dat")
    throat_mach = last_data_row(post, "throatProbes/*/Ma")

    log = (case / "log.foamRun").read_text(encoding="utf-8", errors="replace")
    times = re.findall(r"^Time = (" + FLOAT + r")", log, re.MULTILINE)
    max_co = re.findall(r"Courant Number mean: " + FLOAT + r" max: (" + FLOAT + r")", log)
    max_ma_log = (case / "log.cellMaxMa").read_text(encoding="utf-8", errors="replace")
    max_u_log = (case / "log.cellMaxU").read_text(encoding="utf-8", errors="replace")
    ma_values = re.findall(r"max\(all\).*?=\s*(" + FLOAT + r")", max_ma_log)
    u_values = re.findall(r"max\(all\).*?=\s*(" + FLOAT + r")", max_u_log)

    scale = 360.0 / float(meta.get("wedge_total_degrees", "5"))

    front_p = front[1] if front and len(front) > 1 else None
    rear_p = rear[1] if rear and len(rear) > 1 else None
    row: dict[str, object] = {
        "case": case.name,
        **meta,
        "completed_time_s": float(times[-1]) if times else None,
        "max_courant": float(max_co[-1]) if max_co else None,
        "front_pressure_pa": front_p,
        "rear_pressure_pa": rear_p,
        "pressure_difference_pa": front_p - rear_p if front_p is not None and rear_p is not None else None,
        "pressure_ratio": front_p / rear_p if front_p is not None and rear_p else None,
        "inlet_mass_flow_kg_s": inlet[1] * scale if inlet and len(inlet) > 1 else None,
        "outlet_mass_flow_kg_s": outlet[1] * scale if outlet and len(outlet) > 1 else None,
        "max_mach": float(ma_values[-1]) if ma_values else None,
        "max_velocity_m_s": float(u_values[-1]) if u_values else None,
        "annulus_front_mach": throat_mach[1] if throat_mach and len(throat_mach) > 1 else None,
        "annulus_mid_mach": throat_mach[2] if throat_mach and len(throat_mach) > 2 else None,
        "annulus_rear_mach": throat_mach[3] if throat_mach and len(throat_mach) > 3 else None,
        "wake_mach": throat_mach[4] if throat_mach and len(throat_mach) > 4 else None,
    }
    # forces.dat is time + three pressure-force components + three viscous +
    # porous components in parenthesized groups. Regex flattening makes Fx the
    # second number.
    row["pod_pressure_force_x_n"] = forces[1] * scale if forces and len(forces) > 1 else None
    row["pressure_drag_energy_kwh_per_vehicle_km"] = (
        float(row["pod_pressure_force_x_n"]) / 3600.0
        if row["pod_pressure_force_x_n"] is not None else None
    )
    pod_area = 3.141592653589793 * float(meta["pod_diameter_m"]) ** 2 / 4.0
    expected_pressure_force = (
        float(row["pressure_difference_pa"]) * pod_area
        if row["pressure_difference_pa"] is not None else None
    )
    row["pressure_force_closure_relative_error"] = (
        abs(float(row["pod_pressure_force_x_n"]) - expected_pressure_force)
        / max(abs(expected_pressure_force), 1e-30)
        if expected_pressure_force is not None and row["pod_pressure_force_x_n"] is not None else None
    )
    annulus_values = [row.get("annulus_front_mach"), row.get("annulus_mid_mach"), row.get("annulus_rear_mach")]
    annulus_values = [float(value) for value in annulus_values if value is not None]
    row["annulus_choked"] = max(annulus_values, default=0.0) >= 1.0
    if row["annulus_choked"]:
        labels = ["front", "mid", "rear"]
        row["choking_location"] = labels[max(range(len(annulus_values)), key=annulus_values.__getitem__)]
    elif row.get("wake_mach") is not None and float(row["wake_mach"]) >= 1.0:
        row["choking_location"] = "wake_only_at_probes"
    else:
        row["choking_location"] = "none_at_probes"
    if row["inlet_mass_flow_kg_s"] is not None and row["outlet_mass_flow_kg_s"] is not None:
        denom = max(abs(float(row["inlet_mass_flow_kg_s"])), 1e-30)
        row["boundary_mass_flow_relative_imbalance"] = abs(
            float(row["inlet_mass_flow_kg_s"]) + float(row["outlet_mass_flow_kg_s"])
        ) / denom
    else:
        row["boundary_mass_flow_relative_imbalance"] = None
    return row


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--results", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    rows = [parse_case(case) for case in sorted(args.results.glob("case_*")) if case.is_dir()]
    fields: list[str] = []
    for row in rows:
        for key in row:
            if key not in fields:
                fields.append(key)
    with args.output.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)
    print(f"Wrote {len(rows)} CFD rows to {args.output}")


if __name__ == "__main__":
    main()
