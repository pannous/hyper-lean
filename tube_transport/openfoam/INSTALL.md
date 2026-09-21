# Installed OpenFOAM environment

OpenFOAM is installed in a dedicated native-ARM64 Multipass instance, following
the OpenFOAM Foundation's macOS and Ubuntu package route:

- official macOS instructions: <https://openfoam.org/download/macos/>
- official OpenFOAM 14 Ubuntu package instructions:
  <https://openfoam.org/download/14-ubuntu/>

Verified environment:

| item | value |
|---|---|
| Multipass instance | `openfoam` |
| guest | Ubuntu 22.04 LTS, `aarch64` |
| resources | 6 CPUs, 8 GB RAM, 60 GB disk |
| OpenFOAM | 14, Foundation package build `20260724` |
| installation | `/opt/openfoam14` |

The installed shell configuration sources `/opt/openfoam14/etc/bashrc` from
the guest user's `.bashrc`.

## Reproduce

On an Apple Silicon Mac with Multipass installed:

```bash
multipass launch -c 6 -m 8G -d 60G -n openfoam jammy
multipass exec openfoam -- sudo wget -qO \
  /etc/apt/trusted.gpg.d/openfoam.asc https://dl.openfoam.org/gpg.key
multipass exec openfoam -- sudo add-apt-repository -y \
  "http://dl.openfoam.org/ubuntu main dev"
multipass exec openfoam -- sudo apt-get update
multipass exec openfoam -- sudo env DEBIAN_FRONTEND=noninteractive \
  apt-get install -y openfoam14
```

Then add this line to `/home/ubuntu/.bashrc` inside the guest:

```bash
. /opt/openfoam14/etc/bashrc
```

## Verify

```bash
multipass exec openfoam -- bash -lc \
  '. /opt/openfoam14/etc/bashrc; foamVersion; foamRun -help'
```

Installation validation also ran the packaged
`incompressibleFluid/pitzDailySteady` tutorial through `blockMesh`, `foamRun`
and `checkMesh`; the solver converged in 287 SIMPLE iterations and the mesh
reported `Mesh OK`.

The instance is intentionally left running for repeat sweeps.  Manage it with:

```bash
multipass stop openfoam
multipass start openfoam
multipass shell openfoam
```

