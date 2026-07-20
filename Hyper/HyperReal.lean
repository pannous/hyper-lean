import Hyper.HyperList
import Hyper.HyperClass

/-!
`HyperReal` — canonical name for *the* reference hyperreal model.

The project has explored several representations (`HyperList`, `HyperFun`,
`HyperGeneral`, `HyperKeisler`, ...). `HyperList` is currently the most
developed — canonical sorted normal form, decidable equality/order, 50+
proved lemmas, gauging and standard-part facts — so it is treated as the
reference model here.

Other code should depend on "the hyperreal model" by importing this file and
using `HyperReal`/`ε`/`ω`, rather than importing `HyperList` directly. If a
different backend ever supersedes it as reference, only the `abbrev` below
needs to change — call sites don't.

This file also supplies the one instance that makes the reference model
usable through the implementation-independent interface: once
`IsHyperReal HyperReal` exists, every generic fact in `Hyper/HyperBasics.lean`
holds for it automatically, with no re-proof.
-/

namespace Hypers

/-- The reference hyperreal type. Currently `HyperList`. -/
abbrev HyperReal := HyperList

end Hypers

export Hypers (HyperReal)

open Hypers

instance : IsHyperReal HyperReal where
  eps := ε
  omega := ω
  eps_pos := by native_decide
  eps_lt_one := by native_decide
  eps_lt_omega := by native_decide
  eps_sq_lt_eps := by native_decide
  eps_mul_omega := by native_decide
  omega_mul_eps := by native_decide
  eps_add_eps := by native_decide
  eps_add_eps_add_eps := by native_decide
  omega_add_omega := by native_decide
  eps_sub_eps := by native_decide
  neg_eps_add_eps := by native_decide
  eps_add_zero := by native_decide
  zero_add_omega := by native_decide
  eps_sq_ne_eps := by native_decide
  eps_ne_zero := by native_decide
  eps_ne_omega := by native_decide
  eps_ne_one := by native_decide
