-- Ideally the proofs here should no longer depend on the specific implementation of our hyper real numbers only on the axioms which should hold in all cases
import Hyper.HyperReal
-- import Hyper.HyperGeneral
import Mathlib.Data.Real.Basic

open Hypers

-- ═══════════════════════════════════════════════════════════════════════════
-- Simple evals: ε, ω arithmetic and gauging on the reference HyperReal model.
-- ═══════════════════════════════════════════════════════════════════════════

#eval (ε : HyperReal)              -- [(1, -1)]
#eval (ε * ω : HyperReal)           -- 1
#eval (ε + ε + ε : HyperReal)       -- 3ε

example : (ε : HyperReal) * ω = 1 := by native_decide
example : (0 : HyperReal) < ε := by native_decide
example : ε < (ω : HyperReal) := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- More advanced: the implementation-independent IsHyperReal facts, which
-- hold here purely by instance resolution against Hyper.HyperReal's
-- `instance : IsHyperReal HyperReal` — no reproof, valid for any future
-- backend that supplies the same instance.
-- ═══════════════════════════════════════════════════════════════════════════

open IsHyperReal in
example : (eps : HyperReal) * omega = omega * eps := eps_omega_comm
open IsHyperReal in
example : (eps : HyperReal) < omega := eps_lt_omega
open IsHyperReal in
example : (eps : HyperReal) * eps ≠ eps := eps_sq_ne_eps
