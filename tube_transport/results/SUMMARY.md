# Screening results: low-pressure tube gas management

These are reduced-order results. Rows at or near choking are candidates for CFD, not validated designs.

## Central 1.5 m pod / 2.0 m tube result

The geometric blockage ratio is **0.5625** and the free annulus is **1.374 m²**.

| speed (m/s) | front/rear p | max Mach | Kantrowitz capacity | energy (kWh/vehicle-km) | flags |
|---:|---:|---:|---:|---:|---|
| 50 | 1.037 | 0.227 | 1.760 | 0.0241 |  |
| 100 | 1.148 | 0.448 | 0.914 | 0.0971 | kantrowitz_limit;nonlinear_acoustic_pulse |
| 150 | 1.337 | 0.657 | 0.648 | 0.2206 | kantrowitz_limit;nonlinear_acoustic_pulse |
| 200 | 1.610 | 0.854 | 0.529 | 0.3979 | kantrowitz_limit;nonlinear_acoustic_pulse;reduced_model_invalid |
| 250 | 1.973 | 1.000 | 0.470 | 0.6319 | choked_restriction;kantrowitz_limit;nonlinear_acoustic_pulse;reduced_model_invalid |
| 300 | 2.368 | 1.000 | 0.444 | 0.8933 | choked_restriction;kantrowitz_limit;nonlinear_acoustic_pulse;reduced_model_invalid |
| 350 | 2.763 | 1.000 | 0.438 | 1.1664 | choked_restriction;kantrowitz_limit;nonlinear_acoustic_pulse;reduced_model_invalid |

The ideal Kantrowitz ratio is independent of absolute pressure. Lower pressure reduces mass and energy, but not the volume-flow or area requirement.

## Experiment B: dedicated bypass area for 5% pressure difference

| speed (m/s) | additional bypass area (m²) |
|---:|---:|
| 50 | 0.000 |
| 100 | 1.115 |
| 150 | 2.455 |
| 200 | 3.795 |
| 250 | 5.136 |
| 300 | 6.476 |
| 350 | 7.816 |

This is a best-case effective-area estimate. A real long bypass with bends, friction, valves and pump stations needs more area or active pressure rise.

## Experiment C: integrated ducts

Partitioning exactly the same free cross-section does not create flow capacity. In this model it performs worse than an unobstructed annulus because walls and entrances lower the discharge coefficient. Integrated ducts become interesting only when they reclaim space that was not otherwise a usable flow path, or when they enable active control.

## Experiment D: stationary pumping

At 200 m/s the pod displaces **353.4 m³/s**. Keeping a return path below Mach 0.3 needs about **3.43 m²**. Pump power falls strongly with pressure, but machinery still has to handle the full volume flow. Rows above Mach 0.3 should not be interpreted with the incompressible loss formula.

## Experiment E: compliant local reservoirs

For 10 m station spacing, each station must sweep **17.67 m³**. A passive gas accumulator limited to 5% pressure change would need approximately **494.8 m³** of gas volume per station. The invariant displaced volume is **1767.1 m³ per vehicle-km**.

The ideal compliance lowers acoustic impedance and wave speed, but it stores rather than destroys the pulse. Any damping or hysteresis becomes propulsion energy loss.

## Total-system cost sensitivity

`cost_proxy.csv` combines normalized tube structure, vacuum volume, bypass area, propulsion energy and maintenance terms. The weight sets are disclosed in `config/default.json`; the index is deliberately dimensionless and must not be read as a monetary estimate.

At 300 m/s and 0.01 atm, with bypass sized to the 5% pressure target:

| weighting scenario | minimum-index tube (m) | required bypass (m²) | cost proxy |
|---|---:|---:|---:|
| balanced | 3.0 | 2.003 | 1.219 |
| capital_heavy | 3.0 | 2.003 | 1.177 |
| diameter_dominant | 1.7 | 7.469 | 0.663 |
| energy_heavy | 3.0 | 2.003 | 1.154 |

The winner changes only in the deliberately diameter-dominant scenario. That is the useful economic result: a small tube is not automatically cheaper once the several-square-metre return path is priced, and the decision depends on calibrated civil/structural costs rather than aerodynamics alone.

## Numerical acoustic check

| case | peak pressure (Pa) | wave speed (m/s) | volume-balance error (m³ equivalent) |
|---|---:|---:|---:|
| baseline | 274.91 | 343.23 | 9.127e-16 |
| compliant_5pct | 28.55 | 83.86 | 2.109e-15 |

## OpenFOAM 14 axisymmetric-wedge screening

These are inviscid, abrupt-piston, early-transient snapshots before the initial wave reaches the far boundaries. They are useful for locating the compressible transition, not for final drag design.

| speed (m/s) | front/rear p | annulus Mach front/mid/rear | global max Mach | choking location | pressure force (N) | force closure error | mass-flow imbalance |
|---:|---:|---:|---:|---|---:|---:|---:|
| 150 | 1.880 | 0.665 / 0.812 / 0.906 | 1.055 | wake_only_at_probes | 1143.4 | 1.27e-03 | 2.03e-09 |
| 250 | 3.696 | 0.786 / 0.920 / 1.212 | 1.690 | rear | 2478.9 | 1.27e-03 | 3.70e-05 |

At 150 m/s the sampled annulus remains subsonic but the abrupt trailing-edge wake just exceeds Mach 1. At 250 m/s the rear annulus is already supersonic. This brackets the transition and makes 200 m/s the next convergence/refinement point.

## Decision for CFD

Prioritize a refined 2.0 m-tube case at 200 m/s, then compare the open annulus against a bypass with at least the calculated effective area. Very small bypasses and small local reservoirs are already rejected by continuity.

## Conservation checks

- All quasi-steady rows solve mass flow to a relative residual recorded in CSV.
- Pressure work `delta_p * Q` equals pressure-drag power `F * V` by construction; the residual is recorded.
- The acoustic source/sink pair has zero net injected volume; its residual is shown above.
- Compliance capacity is tied to `A_pod * station spacing`; no hydraulic multiplier changes that swept-volume requirement.
