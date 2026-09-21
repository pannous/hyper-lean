"""Conservative 1-D acoustic transmission-line experiment."""

from __future__ import annotations

from dataclasses import dataclass
import math

import numpy as np

from .model import Air, Geometry


@dataclass(frozen=True)
class AcousticResult:
    time_s: np.ndarray
    peak_pressure_pa: np.ndarray
    final_pressure_pa: np.ndarray
    mass_balance_equivalent_m3: float
    effective_wave_speed_m_s: float
    dx_m: float
    dt_s: float


def simulate_periodic_line(
    geometry: Geometry,
    speed_m_s: float,
    pressure_pa: float,
    duration_s: float = 0.6,
    line_length_m: float = 400.0,
    cells: int = 800,
    added_compliance_per_m_m3_pa: float = 0.0,
    damping_per_s: float = 0.15,
    air: Air | None = None,
) -> AcousticResult:
    """Simulate a moving pod as equal volume injection and extraction.

    Periodic boundaries remove boundary reflections as a confounder.  Equal
    source and sink strengths make global gas-volume conservation explicit.
    This linear model is invalid once gauge pressure is no longer small
    relative to absolute pressure.
    """
    air = air or Air()
    if cells < 32 or duration_s <= 0:
        raise ValueError("positive duration and at least 32 cells required")
    dx = line_length_m / cells
    rho = air.density(pressure_pa)
    base_c_per_m = geometry.tube_area_m2 / (rho * air.sound_speed_m_s**2)
    c_per_m = base_c_per_m + added_compliance_per_m_m3_pa
    l_per_m = rho / geometry.tube_area_m2
    wave_speed = 1.0 / math.sqrt(l_per_m * c_per_m)
    dt = 0.42 * dx / wave_speed
    steps = max(1, int(math.ceil(duration_s / dt)))
    dt = duration_s / steps

    pressure = np.zeros(cells, dtype=float)
    volume_flow_edges = np.zeros(cells, dtype=float)
    node_compliance = c_per_m * dx
    edge_inertance = l_per_m * dx
    q_pod = geometry.pod_area_m2 * speed_m_s
    pod_cells = max(1, int(round(geometry.pod_length_m / dx)))
    sigma_cells = max(1.0, 0.75 * pod_cells)
    indices = np.arange(cells)

    sample_stride = max(1, steps // 600)
    times: list[float] = []
    peaks: list[float] = []

    def periodic_gaussian(center: float) -> np.ndarray:
        distance = np.minimum(np.abs(indices - center), cells - np.abs(indices - center))
        weights = np.exp(-0.5 * (distance / sigma_cells) ** 2)
        return weights / weights.sum()

    for step in range(steps):
        time = step * dt
        volume_flow_edges += dt * (pressure - np.roll(pressure, -1)) / edge_inertance
        volume_flow_edges *= math.exp(-damping_per_s * dt)

        rear_center = (0.25 * cells + speed_m_s * time / dx) % cells
        front_center = (rear_center + pod_cells) % cells
        source = q_pod * (periodic_gaussian(front_center) - periodic_gaussian(rear_center))
        divergence = np.roll(volume_flow_edges, 1) - volume_flow_edges
        pressure += dt * (divergence + source) / node_compliance

        if step % sample_stride == 0 or step == steps - 1:
            times.append(time + dt)
            peaks.append(float(np.max(np.abs(pressure))))

    # Integral C' p dx has units of displaced volume.  It should remain zero.
    balance = abs(float(np.sum(pressure) * node_compliance))
    return AcousticResult(
        time_s=np.asarray(times),
        peak_pressure_pa=np.asarray(peaks),
        final_pressure_pa=pressure,
        mass_balance_equivalent_m3=balance,
        effective_wave_speed_m_s=wave_speed,
        dx_m=dx,
        dt_s=dt,
    )
