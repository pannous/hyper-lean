# OpenFOAM 14 screening case

This directory contains a generated, inexpensive axisymmetric-wedge CFD case.
The pod is stationary, the incoming air moves at pod speed, and all solid
surfaces are inviscid slip boundaries.  The geometry is an abrupt 5 m long
piston inside a straight tube.  This isolates compressible blockage and
pressure drag; it does not model boundary layers, turbulence, pod motion,
leakage, rarefaction, or a streamlined nose/tail.

The mesh is five structured blocks with a one-cell wedge angle and long
upstream/downstream buffer regions.  The reported state is an early transient
snapshot before the initial pressure wave reaches a far boundary; it is not a
claimed steady solution.  Separate pod
front, side and rear patches permit pressure averages and force integration.
The case records:

- pressure force on the pod;
- front and rear area-average pressure;
- inlet/outlet mass flow;
- pressure/velocity probes;
- the Mach-number field.

`run_openfoam.sh` generates and runs two priority points for the 1.5 m pod in
a 2.0 m tube at 0.01 atm: 150 m/s (pre-choke screening) and 250 m/s (predicted
choked).  Both use the same mesh so differences are attributable to operating
conditions rather than remeshing.

The cases live on the case-sensitive filesystem inside the `openfoam`
Multipass VM.  Logs and function-object tables are copied back to
`openfoam/results/`.

Run:

```bash
./run_openfoam.sh
```

Generate another case without running it:

```bash
PYTHONPATH=../src python3 generate_case.py \
  --speed 200 --pressure-atm 0.01 --tube-diameter 2.0 \
  --output generated/case_D2_V200_P0p01
```

The result is a screening CFD calculation. A later moving-mesh calculation,
mesh/time-step/domain convergence, longer non-reflecting boundaries and a
viscous/turbulent model are required before using absolute drag values in an
engineering design.
