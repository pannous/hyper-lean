import Lake
open Lake DSL

package «Hyper» where

@[default_target]
lean_lib Hyper {
  roots := #[`Hyper]
}

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"
require Cli from git "https://github.com/mhuisi/lean4-cli.git" @ "nightly"
meta if get_config? doc = some "on" then -- dev is so not everyone has to build it
  require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"
