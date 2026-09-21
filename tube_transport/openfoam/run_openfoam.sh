#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"

instance=openfoam
remote_root=/home/ubuntu/tube_transport_cfd
mkdir -p generated results

run_case() {
    local speed=$1
    local case_name="case_D2_V${speed}_P0p01"
    local local_case="$PWD/generated/$case_name"
    local local_result="$PWD/results/$case_name"
    local remote_case="$remote_root/$case_name"

    python3 generate_case.py \
        --speed "$speed" \
        --pressure-atm 0.01 \
        --tube-diameter 2.0 \
        --output "$local_case"

    multipass exec "$instance" -- mkdir -p "$remote_root"
    multipass exec "$instance" -- rm -rf "$remote_case"
    multipass transfer --recursive "$local_case" "$instance:$remote_root"

    multipass exec "$instance" -- bash -lc ". /opt/openfoam14/etc/bashrc
        cd '$remote_case'
        blockMesh > log.blockMesh 2>&1
        checkMesh > log.checkMesh 2>&1
        grep -q 'Mesh OK' log.checkMesh
        foamRun > log.foamRun 2>&1
        foamPostProcess -func MachNo -latestTime > log.MachNo 2>&1
        foamPostProcess -func throatProbes -latestTime > log.throatProbes 2>&1
        foamPostProcess -func 'cellMax(Ma)' -latestTime > log.cellMaxMa 2>&1
        foamPostProcess -func 'mag(U)' -latestTime > log.magU 2>&1
        foamPostProcess -func 'cellMax(mag(U))' -latestTime > log.cellMaxU 2>&1
    "

    mkdir -p "$local_result"
    multipass transfer "$instance:$remote_case/log.blockMesh" "$local_result/"
    multipass transfer "$instance:$remote_case/log.checkMesh" "$local_result/"
    multipass transfer "$instance:$remote_case/log.foamRun" "$local_result/"
    multipass transfer "$instance:$remote_case/log.MachNo" "$local_result/"
    multipass transfer "$instance:$remote_case/log.throatProbes" "$local_result/"
    multipass transfer "$instance:$remote_case/log.cellMaxMa" "$local_result/"
    multipass transfer "$instance:$remote_case/log.magU" "$local_result/"
    multipass transfer "$instance:$remote_case/log.cellMaxU" "$local_result/"
    multipass transfer "$instance:$remote_case/CASE_METADATA.txt" "$local_result/"
    if multipass exec "$instance" -- test -d "$remote_case/postProcessing"; then
        multipass transfer --recursive "$instance:$remote_case/postProcessing" "$local_result/"
    fi
}

run_case 150
run_case 250

python3 extract_results.py --results results --output results/cfd_summary.csv
echo "OpenFOAM cases complete: $PWD/results/cfd_summary.csv"
