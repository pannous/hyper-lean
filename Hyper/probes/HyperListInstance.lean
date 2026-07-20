import Hyper.HyperReal

/-!
Sanity check that the `instance : IsHyperReal HyperReal` wired up in
`Hyper/HyperReal.lean` actually makes the generic facts from
`Hyper/HyperBasics.lean` available for the concrete `HyperList` model with no
further proof — pure instance resolution.
-/

open Hypers
open IsHyperReal in
example : (ε : HyperReal) + ε = (1 + 1) * ε := eps_add_eps
open IsHyperReal in
example : (ε : HyperReal) * ω = 1 := eps_mul_omega
open IsHyperReal in
example : (0 : HyperReal) < ε := eps_pos
open IsHyperReal in
example : (ε : HyperReal) ≠ ω := eps_ne_omega
open IsHyperReal in
example : (ε : HyperReal) * ω = ω * ε := eps_omega_comm
