"""Compressible-flow screening model.

The flow network is deliberately simple: a moving pod displaces the geometric
volume rate ``A_pod * V`` and that flow passes from the front control volume to
the rear through one or more effective restrictions.  Isentropic ideal-gas
mass flux is used at each restriction.  Long-duct friction and 3-D losses are
represented only by effective discharge coefficients.
"""

from __future__ import annotations

from dataclasses import dataclass
import math
from typing import Iterable


ATM_PA = 101_325.0


@dataclass(frozen=True)
class Air:
    gamma: float = 1.4
    gas_constant_j_kg_k: float = 287.05
    temperature_k: float = 293.15
    dynamic_viscosity_pa_s: float = 1.81e-5

    @property
    def sound_speed_m_s(self) -> float:
        return math.sqrt(self.gamma * self.gas_constant_j_kg_k * self.temperature_k)

    def density(self, pressure_pa: float) -> float:
        return pressure_pa / (self.gas_constant_j_kg_k * self.temperature_k)


@dataclass(frozen=True)
class Geometry:
    pod_diameter_m: float
    tube_diameter_m: float
    pod_length_m: float = 5.0

    @property
    def pod_area_m2(self) -> float:
        return math.pi * self.pod_diameter_m**2 / 4.0

    @property
    def tube_area_m2(self) -> float:
        return math.pi * self.tube_diameter_m**2 / 4.0

    @property
    def annulus_area_m2(self) -> float:
        return self.tube_area_m2 - self.pod_area_m2

    @property
    def blockage(self) -> float:
        return self.pod_area_m2 / self.tube_area_m2

    @property
    def hydraulic_gap_m(self) -> float:
        return self.tube_diameter_m - self.pod_diameter_m


@dataclass(frozen=True)
class FlowPath:
    name: str
    area_m2: float
    discharge_coefficient: float

    @property
    def effective_area_m2(self) -> float:
        return max(0.0, self.area_m2) * self.discharge_coefficient


@dataclass(frozen=True)
class FlowResult:
    pressure_front_pa: float
    pressure_rear_pa: float
    pressure_difference_pa: float
    pressure_ratio: float
    displaced_volume_flow_m3_s: float
    mass_flow_kg_s: float
    max_gas_velocity_m_s: float
    max_mach: float
    choked: bool
    choking_location: str
    drag_n: float
    pressure_drag_n: float
    shape_drag_n: float
    power_w: float
    energy_kwh_per_vehicle_km: float
    mass_conservation_relative_error: float
    power_conservation_relative_error: float
    kantrowitz_capacity_ratio: float
    acoustic_overpressure_pa: float
    acoustic_transit_s_per_km: float
    reynolds_gap: float
    flags: tuple[str, ...]


def blockage_ratio(pod_diameter_m: float, tube_diameter_m: float) -> float:
    if pod_diameter_m <= 0 or tube_diameter_m <= 0:
        raise ValueError("diameters must be positive")
    if pod_diameter_m >= tube_diameter_m:
        raise ValueError("pod must be smaller than tube")
    return (pod_diameter_m / tube_diameter_m) ** 2


def critical_pressure_ratio(gamma: float) -> float:
    return (2.0 / (gamma + 1.0)) ** (gamma / (gamma - 1.0))


def isentropic_mass_flux(
    upstream_pressure_pa: float,
    downstream_pressure_pa: float,
    air: Air,
) -> tuple[float, float, bool, float]:
    """Return mass flux, throat Mach, choked flag and throat temperature.

    Upstream temperature is treated as stagnation temperature.  This is an
    orifice/nozzle screening relation, not a long-duct Fanno solution.
    """
    if upstream_pressure_pa <= 0 or downstream_pressure_pa <= 0:
        raise ValueError("absolute pressures must be positive")
    if downstream_pressure_pa > upstream_pressure_pa:
        raise ValueError("downstream pressure cannot exceed upstream pressure")

    gamma = air.gamma
    ratio = downstream_pressure_pa / upstream_pressure_pa
    critical = critical_pressure_ratio(gamma)
    common = upstream_pressure_pa * math.sqrt(gamma / (air.gas_constant_j_kg_k * air.temperature_k))
    if ratio <= critical:
        factor = (2.0 / (gamma + 1.0)) ** ((gamma + 1.0) / (2.0 * (gamma - 1.0)))
        temperature = air.temperature_k * 2.0 / (gamma + 1.0)
        return common * factor, 1.0, True, temperature

    inside = (2.0 / (gamma - 1.0)) * (ratio ** (2.0 / gamma) - ratio ** ((gamma + 1.0) / gamma))
    flux = upstream_pressure_pa * math.sqrt(gamma * max(0.0, inside) / (air.gas_constant_j_kg_k * air.temperature_k))
    mach = math.sqrt(2.0 / (gamma - 1.0) * (ratio ** (-(gamma - 1.0) / gamma) - 1.0))
    temperature = air.temperature_k / (1.0 + 0.5 * (gamma - 1.0) * mach**2)
    return flux, mach, False, temperature


def _network_mass_flow(
    upstream_pressure_pa: float,
    downstream_pressure_pa: float,
    paths: Iterable[FlowPath],
    air: Air,
) -> tuple[float, float, bool, str, float]:
    flux, mach, choked, throat_temperature = isentropic_mass_flux(
        upstream_pressure_pa, downstream_pressure_pa, air
    )
    active = [path for path in paths if path.effective_area_m2 > 0]
    mass_flow = flux * sum(path.effective_area_m2 for path in active)
    location = "+".join(path.name for path in active) if choked else "none"
    return mass_flow, mach, choked, location, throat_temperature


def solve_front_pressure(
    required_mass_flow_kg_s: float,
    rear_pressure_pa: float,
    paths: Iterable[FlowPath],
    air: Air,
) -> tuple[float, float, bool, str, float, float]:
    """Solve front pressure such that restriction flow matches displacement."""
    paths = tuple(paths)
    effective_area = sum(path.effective_area_m2 for path in paths)
    if required_mass_flow_kg_s < 0:
        raise ValueError("required flow must be nonnegative")
    if effective_area <= 0:
        return math.inf, 0.0, True, "no_flow_path", air.temperature_k, math.inf
    if required_mass_flow_kg_s == 0:
        return rear_pressure_pa, 0.0, False, "none", air.temperature_k, 0.0

    low = rear_pressure_pa * (1.0 + 1e-12)
    high = rear_pressure_pa * 2.0
    for _ in range(100):
        flow, *_ = _network_mass_flow(high, rear_pressure_pa, paths, air)
        if flow >= required_mass_flow_kg_s:
            break
        high *= 2.0
    else:
        raise RuntimeError("could not bracket front pressure")

    for _ in range(100):
        mid = 0.5 * (low + high)
        flow, *_ = _network_mass_flow(mid, rear_pressure_pa, paths, air)
        if flow < required_mass_flow_kg_s:
            low = mid
        else:
            high = mid

    pressure = high
    flow, mach, choked, location, temperature = _network_mass_flow(
        pressure, rear_pressure_pa, paths, air
    )
    error = abs(flow - required_mass_flow_kg_s) / required_mass_flow_kg_s
    return pressure, mach, choked, location, temperature, error


def required_effective_area_for_pressure_limit(
    required_mass_flow_kg_s: float,
    rear_pressure_pa: float,
    maximum_relative_difference: float,
    air: Air,
) -> float:
    if maximum_relative_difference <= 0:
        raise ValueError("pressure tolerance must be positive")
    front = rear_pressure_pa * (1.0 + maximum_relative_difference)
    flux, *_ = isentropic_mass_flux(front, rear_pressure_pa, air)
    return required_mass_flow_kg_s / flux


def kantrowitz_capacity_ratio(
    geometry: Geometry,
    speed_m_s: float,
    pressure_pa: float,
    air: Air,
) -> float:
    """Ideal throat capacity / required pod-frame through-flow.

    A value below one means the annular throat cannot pass the upstream
    pod-frame mass flux without a pressure rise.  Pressure cancels in the
    ideal-gas result, but is retained here to expose the calculation.
    """
    rho = air.density(pressure_pa)
    inlet_mach = speed_m_s / air.sound_speed_m_s
    stagnation_temperature = air.temperature_k * (1.0 + 0.5 * (air.gamma - 1.0) * inlet_mach**2)
    stagnation_pressure = pressure_pa * (1.0 + 0.5 * (air.gamma - 1.0) * inlet_mach**2) ** (
        air.gamma / (air.gamma - 1.0)
    )
    factor = math.sqrt(air.gamma / (air.gas_constant_j_kg_k * stagnation_temperature))
    factor *= (2.0 / (air.gamma + 1.0)) ** ((air.gamma + 1.0) / (2.0 * (air.gamma - 1.0)))
    capacity = geometry.annulus_area_m2 * stagnation_pressure * factor
    required = rho * speed_m_s * geometry.tube_area_m2
    return capacity / required if required > 0 else math.inf


def evaluate_flow(
    geometry: Geometry,
    speed_m_s: float,
    pressure_pa: float,
    paths: Iterable[FlowPath],
    air: Air | None = None,
    shape: str = "piston",
) -> FlowResult:
    air = air or Air()
    if speed_m_s <= 0:
        raise ValueError("speed must be positive")
    if geometry.annulus_area_m2 <= 0:
        raise ValueError("pod leaves no annular area")
    rho = air.density(pressure_pa)
    volume_flow = geometry.pod_area_m2 * speed_m_s
    required_mass_flow = rho * volume_flow
    front, mach, choked, location, throat_temperature, mass_error = solve_front_pressure(
        required_mass_flow, pressure_pa, paths, air
    )
    if math.isfinite(front):
        delta_p = front - pressure_pa
        pressure_drag = delta_p * geometry.pod_area_m2
    else:
        delta_p = math.inf
        pressure_drag = math.inf

    drag_coefficients = {"piston": 0.80, "streamlined": 0.12}
    if shape not in drag_coefficients:
        raise ValueError(f"unknown shape: {shape}")
    shape_drag = 0.5 * rho * speed_m_s**2 * geometry.pod_area_m2 * drag_coefficients[shape]
    drag = pressure_drag + shape_drag
    power = drag * speed_m_s
    energy_kwh_per_km = drag / 3600.0

    local_sound_speed = math.sqrt(air.gamma * air.gas_constant_j_kg_k * throat_temperature)
    gas_velocity = mach * local_sound_speed
    acoustic_dp = rho * air.sound_speed_m_s * speed_m_s * geometry.blockage
    pressure_power = delta_p * volume_flow if math.isfinite(delta_p) else math.inf
    drag_power = pressure_drag * speed_m_s if math.isfinite(pressure_drag) else math.inf
    power_error = (
        abs(pressure_power - drag_power) / max(abs(pressure_power), 1e-30)
        if math.isfinite(pressure_power)
        else math.inf
    )
    reynolds = rho * speed_m_s * geometry.hydraulic_gap_m / air.dynamic_viscosity_pa_s
    capacity_ratio = kantrowitz_capacity_ratio(geometry, speed_m_s, pressure_pa, air)

    flags: list[str] = []
    if choked:
        flags.append("choked_restriction")
    if capacity_ratio < 1.0:
        flags.append("kantrowitz_limit")
    if acoustic_dp > 0.2 * pressure_pa:
        flags.append("nonlinear_acoustic_pulse")
    if mach > 0.8:
        flags.append("reduced_model_invalid")
    if reynolds < 1.0e4:
        flags.append("low_reynolds_or_rarefaction_check")

    return FlowResult(
        pressure_front_pa=front,
        pressure_rear_pa=pressure_pa,
        pressure_difference_pa=delta_p,
        pressure_ratio=front / pressure_pa,
        displaced_volume_flow_m3_s=volume_flow,
        mass_flow_kg_s=required_mass_flow,
        max_gas_velocity_m_s=gas_velocity,
        max_mach=mach,
        choked=choked,
        choking_location=location,
        drag_n=drag,
        pressure_drag_n=pressure_drag,
        shape_drag_n=shape_drag,
        power_w=power,
        energy_kwh_per_vehicle_km=energy_kwh_per_km,
        mass_conservation_relative_error=mass_error,
        power_conservation_relative_error=power_error,
        kantrowitz_capacity_ratio=capacity_ratio,
        acoustic_overpressure_pa=acoustic_dp,
        acoustic_transit_s_per_km=1000.0 / air.sound_speed_m_s,
        reynolds_gap=reynolds,
        flags=tuple(flags),
    )


def pump_power(
    geometry: Geometry,
    speed_m_s: float,
    pressure_pa: float,
    flow_area_m2: float,
    loss_coefficient: float,
    efficiency: float,
    air: Air,
) -> dict[str, float | bool]:
    """Ideal fan power to overcome a prescribed return-path loss.

    It does not claim that a fan can remain efficient at the resulting Mach
    number.  The Mach flag is the principal screening result.
    """
    if flow_area_m2 <= 0 or not (0 < efficiency <= 1):
        raise ValueError("positive flow area and physical efficiency required")
    q = geometry.pod_area_m2 * speed_m_s
    path_velocity = q / flow_area_m2
    rho = air.density(pressure_pa)
    delta_p = 0.5 * loss_coefficient * rho * path_velocity**2
    power = delta_p * q / efficiency
    mach = path_velocity / air.sound_speed_m_s
    return {
        "volume_flow_m3_s": q,
        "path_velocity_m_s": path_velocity,
        "path_mach": mach,
        "pressure_rise_pa": delta_p,
        "shaft_power_w": power,
        "energy_kwh_per_vehicle_km": power / speed_m_s / 3600.0,
        "highly_compressible_path": mach > 0.3,
        "minimum_area_for_mach_0_3_m2": q / (0.3 * air.sound_speed_m_s),
    }


def compliant_station(
    geometry: Geometry,
    spacing_m: float,
    pressure_pa: float,
    target_pressure_fraction: float,
    loss_fraction: float,
    air: Air,
) -> dict[str, float]:
    """Conservation-limited compliant chamber sizing for one station."""
    if spacing_m <= 0 or target_pressure_fraction <= 0:
        raise ValueError("spacing and pressure target must be positive")
    swept_volume = geometry.pod_area_m2 * spacing_m
    target_delta_p = pressure_pa * target_pressure_fraction
    compliance = swept_volume / target_delta_p
    gas_accumulator_volume = air.gamma * pressure_pa * compliance
    stored_energy = 0.5 * target_delta_p * swept_volume
    lost_energy_station = stored_energy * loss_fraction
    stations_per_km = 1000.0 / spacing_m

    base_compliance_per_m = geometry.tube_area_m2 / (air.gamma * pressure_pa)
    added_compliance_per_m = compliance / spacing_m
    inertance_per_m = air.density(pressure_pa) / geometry.tube_area_m2
    total_compliance_per_m = base_compliance_per_m + added_compliance_per_m
    effective_wave_speed = 1.0 / math.sqrt(inertance_per_m * total_compliance_per_m)
    characteristic_impedance = math.sqrt(inertance_per_m / total_compliance_per_m)

    return {
        "swept_volume_per_station_m3": swept_volume,
        "target_pressure_difference_pa": target_delta_p,
        "required_compliance_m3_pa": compliance,
        "equivalent_gas_accumulator_volume_m3": gas_accumulator_volume,
        "stored_energy_per_station_j": stored_energy,
        "lost_energy_per_station_j": lost_energy_station,
        "lost_energy_kwh_per_vehicle_km": lost_energy_station * stations_per_km / 3.6e6,
        "effective_wave_speed_m_s": effective_wave_speed,
        "characteristic_impedance_pa_s_m3": characteristic_impedance,
        "swept_volume_per_vehicle_km_m3": geometry.pod_area_m2 * 1000.0,
    }
