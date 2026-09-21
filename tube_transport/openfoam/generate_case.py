#!/usr/bin/env python3
"""Generate an OpenFOAM 14 axisymmetric piston-in-tube case."""

from __future__ import annotations

import argparse
import math
from pathlib import Path


HEADER = r"""/*--------------------------------*- C++ -*----------------------------------*\
  =========                 |
  \\      /  F ield         | OpenFOAM: The Open Source CFD Toolbox
   \\    /   O peration     | Version:  14
    \\  /    A nd           |
     \\/     M anipulation  |
\*---------------------------------------------------------------------------*/
"""


def foam_file(location: str, object_name: str, class_name: str = "dictionary") -> str:
    return HEADER + f"""FoamFile
{{
    format      ascii;
    class       {class_name};
    location    \"{location}\";
    object      {object_name};
}}
// * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * //

"""


def write(path: Path, contents: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(contents.rstrip() + "\n\n// ************************************************************************* //\n", encoding="utf-8")


def block_mesh_dict(tube_diameter: float, pod_diameter: float, wedge_degrees: float = 2.5) -> str:
    rp = pod_diameter / 2.0
    rt = tube_diameter / 2.0
    if not 0 < rp < rt:
        raise ValueError("pod radius must be between zero and tube radius")
    angle = math.radians(wedge_degrees)
    c, s = math.cos(angle), math.sin(angle)
    # Long buffers keep the early-time screening snapshot free of reflected
    # waves from the finite inlet/outlet boundaries.
    xs = [-30.0, -2.5, 2.5, 30.0]

    vertices: list[tuple[float, float, float]] = []
    vertices.extend((x, 0.0, 0.0) for x in xs)
    vertices.extend((x, rp * c, -rp * s) for x in xs)
    vertices.extend((x, rt * c, -rt * s) for x in xs)
    vertices.extend((x, rp * c, rp * s) for x in xs)
    vertices.extend((x, rt * c, rt * s) for x in xs)
    vertex_text = "\n".join(f"    ({x:.9g} {y:.9g} {z:.9g})" for x, y, z in vertices)

    return foam_file("system", "blockMeshDict") + f"""units [m];

vertices
(
{vertex_text}
);

blocks
(
    // Upstream core and outer annulus
    hex (0 1 5 4 0 1 13 12) (100 30 1) simpleGrading (0.10 0.7 1)
    hex (4 5 9 8 12 13 17 16) (100 24 1) simpleGrading (0.10 1 1)
    // Annular throat beside pod
    hex (5 6 10 9 13 14 18 17) (60 24 1) simpleGrading (1 1 1)
    // Downstream core and outer annulus
    hex (2 3 7 6 2 3 15 14) (100 30 1) simpleGrading (10 0.7 1)
    hex (6 7 11 10 14 15 19 18) (100 24 1) simpleGrading (10 1 1)
);

boundary
(
    inlet
    {{
        type patch;
        faces ((0 0 12 4) (4 12 16 8));
    }}
    outlet
    {{
        type patch;
        faces ((3 7 15 3) (7 11 19 15));
    }}
    tubeWall
    {{
        type wall;
        faces ((8 16 17 9) (9 17 18 10) (10 18 19 11));
    }}
    podFront
    {{
        type wall;
        faces ((1 5 13 1));
    }}
    podSide
    {{
        type wall;
        faces ((5 6 14 13));
    }}
    podRear
    {{
        type wall;
        faces ((2 2 14 6));
    }}
    axis
    {{
        type empty;
        faces ((0 1 1 0) (2 3 3 2));
    }}
    wedgeLow
    {{
        type wedge;
        faces
        (
            (0 4 5 1)
            (4 8 9 5)
            (5 9 10 6)
            (2 6 7 3)
            (6 10 11 7)
        );
    }}
    wedgeHigh
    {{
        type wedge;
        faces
        (
            (0 1 13 12)
            (12 13 17 16)
            (13 14 18 17)
            (2 3 15 14)
            (14 15 19 18)
        );
    }}
);
"""


def generate(output: Path, speed: float, pressure_atm: float, tube_diameter: float,
             pod_diameter: float = 1.5, end_time: float = 0.035) -> None:
    pressure = pressure_atm * 101325.0
    temperature = 293.15
    output.mkdir(parents=True, exist_ok=True)
    write(output / "system/blockMeshDict", block_mesh_dict(tube_diameter, pod_diameter))

    control = foam_file("system", "controlDict") + f"""solver          fluid;
startFrom       startTime;
startTime       0;
stopAt          endTime;
endTime         {end_time:.9g};
deltaT          1e-6;
adjustTimeStep  yes;
maxCo           0.45;
maxDeltaT       2e-5;
writeControl    runTime;
writeInterval   0.005;
purgeWrite      2;
writeFormat     ascii;
writePrecision  9;
writeCompression off;
timeFormat      general;
timePrecision   8;
runTimeModifiable true;

functions
{{
    Ma
    {{
        type MachNo;
        libs (\"libfieldFunctionObjects.so\");
        executeControl writeTime;
        writeControl writeTime;
    }}
    podForces
    {{
        type forces;
        libs (\"libforces.so\");
        writeControl writeTime;
        patches (podFront podSide podRear);
        rho rho;
        p p;
        U U;
        CofR (0 0 0);
        log yes;
    }}
    frontPressure
    {{
        type surfaceFieldValue;
        libs (\"libfieldFunctionObjects.so\");
        writeControl writeTime;
        log yes;
        writeFields no;
        patch podFront;
        operation areaAverage;
        fields (p);
    }}
    rearPressure
    {{
        type surfaceFieldValue;
        libs (\"libfieldFunctionObjects.so\");
        writeControl writeTime;
        log yes;
        writeFields no;
        patch podRear;
        operation areaAverage;
        fields (p);
    }}
    inletMassFlow
    {{
        type surfaceFieldValue;
        libs (\"libfieldFunctionObjects.so\");
        writeControl writeTime;
        log yes;
        writeFields no;
        patch inlet;
        operation sum;
        fields (phi);
    }}
    outletMassFlow
    {{
        type surfaceFieldValue;
        libs (\"libfieldFunctionObjects.so\");
        writeControl writeTime;
        log yes;
        writeFields no;
        patch outlet;
        operation sum;
        fields (phi);
    }}
    pressureProbes
    {{
        type probes;
        libs (\"libsampling.so\");
        writeControl timeStep;
        writeInterval 20;
        fields (p U rho);
        probeLocations
        (
            (-20 0.5 0)
            (-2.6 0.8 0)
            (2.6 0.8 0)
            (20 0.5 0)
        );
    }}
}}
"""
    write(output / "system/controlDict", control)

    schemes = foam_file("system", "fvSchemes") + """ddtSchemes
{
    default Euler;
}
gradSchemes
{
    default Gauss linear;
}
divSchemes
{
    default none;
    div(phi,U) Gauss upwind;
    div(phid,p) Gauss limitedLinear 1;
    div(phi,e) Gauss limitedLinear 1;
    div(phi,K) Gauss limitedLinear 1;
    div(phi,(p|rho)) Gauss limitedLinear 1;
    div(((rho*nuEff)*dev2(T(grad(U))))) Gauss linear;
}
laplacianSchemes
{
    default Gauss linear corrected;
}
interpolationSchemes
{
    default linear;
}
snGradSchemes
{
    default corrected;
}
"""
    write(output / "system/fvSchemes", schemes)

    solution = foam_file("system", "fvSolution") + """solvers
{
    "rho.*"
    {
        solver diagonal;
    }
    "p.*"
    {
        solver smoothSolver;
        smoother symGaussSeidel;
        tolerance 1e-8;
        relTol 0;
    }
    "(U|e).*"
    {
        $p;
        tolerance 1e-8;
        relTol 0;
    }
}
PIMPLE
{
    nOuterCorrectors 2;
    nCorrectors 1;
    nNonOrthogonalCorrectors 0;
    transonic yes;
}
"""
    write(output / "system/fvSolution", solution)

    throat_probes = foam_file("system", "throatProbes") + """type probes;
libs (\"libsampling.so\");
writeControl writeTime;
fields (p U rho Ma);
probeLocations
(
    (-2.4 0.875 0)
    (0 0.875 0)
    (2.4 0.875 0)
    (3.5 0.875 0)
);
"""
    write(output / "system/throatProbes", throat_probes)

    physical = foam_file("constant", "physicalProperties") + """thermoType
{
    type hePsiThermo;
    mixture pureMixture;
    transport const;
    thermo hConst;
    equationOfState perfectGas;
    specie specie;
    energy sensibleInternalEnergy;
}
mixture
{
    specie
    {
        molWeight 28.96;
    }
    thermodynamics
    {
        Cp 1005;
        hf 0;
    }
    transport
    {
        // Inviscid screening case; pressure drag is the target.
        mu 0;
        Pr 0.71;
    }
}
"""
    write(output / "constant/physicalProperties", physical)
    write(output / "constant/momentumTransport", foam_file("constant", "momentumTransport") + "simulationType laminar;")

    common_boundaries = """    tubeWall { type slip; }
    podFront { type slip; }
    podSide { type slip; }
    podRear { type slip; }
    axis { type empty; }
    wedgeLow { type wedge; }
    wedgeHigh { type wedge; }"""
    u = foam_file("0", "U", "volVectorField") + f"""dimensions [velocity];
internalField uniform ({speed:.9g} 0 0);
boundaryField
{{
    inlet {{ type fixedValue; value uniform ({speed:.9g} 0 0); }}
    outlet {{ type zeroGradient; }}
{common_boundaries}
}}
"""
    write(output / "0/U", u)

    p = foam_file("0", "p", "volScalarField") + f"""dimensions [pressure];
internalField uniform {pressure:.9g};
boundaryField
{{
    inlet {{ type fixedValue; value uniform {pressure:.9g}; }}
    outlet
    {{
        type waveTransmissive;
        field p;
        gamma 1.4;
        fieldInf {pressure:.9g};
        lInf 5;
        value uniform {pressure:.9g};
    }}
    tubeWall {{ type zeroGradient; }}
    podFront {{ type zeroGradient; }}
    podSide {{ type zeroGradient; }}
    podRear {{ type zeroGradient; }}
    axis {{ type empty; }}
    wedgeLow {{ type wedge; }}
    wedgeHigh {{ type wedge; }}
}}
"""
    write(output / "0/p", p)

    t = foam_file("0", "T", "volScalarField") + f"""dimensions [temperature];
internalField uniform {temperature};
boundaryField
{{
    inlet {{ type fixedValue; value uniform {temperature}; }}
    outlet {{ type zeroGradient; }}
    tubeWall {{ type zeroGradient; }}
    podFront {{ type zeroGradient; }}
    podSide {{ type zeroGradient; }}
    podRear {{ type zeroGradient; }}
    axis {{ type empty; }}
    wedgeLow {{ type wedge; }}
    wedgeHigh {{ type wedge; }}
}}
"""
    write(output / "0/T", t)

    metadata = f"""speed_m_s={speed}
pressure_atm={pressure_atm}
pressure_pa={pressure}
tube_diameter_m={tube_diameter}
pod_diameter_m={pod_diameter}
blockage_ratio={(pod_diameter / tube_diameter) ** 2}
wedge_total_degrees={2 * 2.5}
end_time_s={end_time}
model=inviscid_axisymmetric_abrupt_piston_early_transient
"""
    write(output / "CASE_METADATA.txt", metadata)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--speed", type=float, required=True)
    parser.add_argument("--pressure-atm", type=float, required=True)
    parser.add_argument("--tube-diameter", type=float, required=True)
    parser.add_argument("--pod-diameter", type=float, default=1.5)
    parser.add_argument("--end-time", type=float, default=0.035)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    generate(args.output, args.speed, args.pressure_atm, args.tube_diameter, args.pod_diameter, args.end_time)


if __name__ == "__main__":
    main()
