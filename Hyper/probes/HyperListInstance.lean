import Hyper.HyperList
import Hyper.HyperClass

/-!
Backend proof obligation: show the concrete `HyperList` model (`R*`)
satisfies the implementation-independent `IsHyperReal` interface. This is the
*only* file that knows `eps`/`omega` are lists and that `native_decide` is an
appropriate way to check facts about them — `Hyper/HyperBasics.lean` never
sees any of that.
-/

open Hypers

instance : IsHyperReal R* where
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

-- With the instance above in scope, every generic fact from `HyperBasics.lean`
-- now holds for `R*` automatically — no re-proof, just instance resolution.
open IsHyperReal in
example : (ε : R*) + ε = (1 + 1) * ε := eps_add_eps
open IsHyperReal in
example : (ε : R*) * ω = 1 := eps_mul_omega
open IsHyperReal in
example : (0 : R*) < ε := eps_pos
open IsHyperReal in
example : (ε : R*) ≠ ω := eps_ne_omega
