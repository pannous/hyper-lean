# Low-pressure tube transport screening model

This project screens infrastructure-side gas-management concepts for a small
passenger pod before committing to expensive CFD.  It deliberately separates
three evidence levels:

1. **Analytical / quasi-steady:** ideal-gas continuity plus a compressible
   orifice model.  This is useful for eliminating impossible area/volume
   concepts and locating likely choking.
2. **Inexpensive numerical:** a conservative 1-D acoustic transmission line
   with a moving source/sink pair and optional distributed compliance.
3. **CFD:** an OpenFOAM 14 axisymmetric-wedge case for selected configurations.

The reduced models are screening tools, not a substitute for moving-mesh,
turbulent, rarefied-gas CFD or experiments.  In particular, the effective
discharge coefficients lump together entrance, exit, bend and friction losses.

## Baseline assumptions

- 1.5 m diameter, 5 m long pod
- 293.15 K air, `gamma = 1.4`, `R = 287.05 J/(kg K)`
- speeds 50--350 m/s
- tube diameters 1.7, 1.8, 2.0, 2.2, 2.5 and 3.0 m
- pressures 0.001, 0.003, 0.01, 0.03 and 0.1 atm
- piston and streamlined form-drag sensitivity cases
- "small pressure difference" means 5% of the undisturbed absolute pressure

The volume rate which must be accommodated is always

`Q = A_pod * velocity`.

Lowering pressure lowers mass flow and aerodynamic power, but it does **not**
lower this geometric volume-flow requirement.

## Run

From this directory:

```bash
./run_all.sh
```

This runs unit tests, all A--E sweeps, the acoustic cases, and writes CSV,
Markdown and PNG outputs under `results/`.

`cost_proxy.csv` adds a dimensionless sensitivity screen across tube structure,
vacuum volume, bypass infrastructure, propulsion energy and maintenance.  It
uses disclosed weight sets from the config.  It is not a bill of materials or
a currency-valued lifecycle-cost estimate.  The simple tube structure term
scales with diameter squared; real external-pressure buckling, supports,
material choice, construction and land costs must replace that placeholder
before an economic decision.

The OpenFOAM case is generated and run separately:

```bash
./openfoam/run_openfoam.sh
```

It expects the Multipass instance named `openfoam`, with OpenFOAM 14 installed
at `/opt/openfoam14`.  The script transfers a generated case into the VM,
checks the mesh, runs it, and copies logs/results back.  See
`openfoam/README.md` for scope and limitations.

## Experiments

- **A -- ordinary annulus:** tube sweep, blockage, pressure rise, drag and
  choking indicators.
- **B -- dedicated return channel:** independent bypass-area sweep and direct
  solution for the area needed to hold front/rear pressure difference to 5%.
- **C -- integrated return ducts:** partitioned ducts compared with an open
  annulus at the same vessel diameter and geometric area.
- **D -- stationary pumping:** fan/pump power needed to overcome return-path
  losses at the required volume flow, compared with a restricted onboard path.
- **E -- compliant reservoirs:** swept volume, compliance, stored/lost energy
  and acoustic impedance.  A chamber station serving spacing `s` must accept
  approximately `A_pod * s`; that conservation constraint is never waived.

## Important validity flags

Rows contain `flags`.  Treat any row with `reduced_model_invalid` or
`highly_compressible_path` as a request for higher fidelity, not a prediction.
The model also flags choking, nonlinear acoustic pulses and cases where an
idealized compliant chamber would need implausibly large swept volume.
