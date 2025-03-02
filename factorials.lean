import Mathlib.Data.Real.Basic -- NON-COMPUTABLE
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Init.Data.Float
import Init.Data.Nat.Basic --  basic operations built-in
import Mathlib.Data.Nat.Basic --stronger lemmas, theorem automation, or advanced properties
import Lean

set_option diagnostics true
set_option diagnostics.threshold 1000
#eval Lean.versionString


-- def tau : ℝ := 2 * 3.141592653589793
def Float.pi : Float := 3.1415926535897932385
def tau := 2 * Float.pi


def factorial : Nat -> Nat -- ℕ → ℕ
| 0 => 1
| (n + 1) => (n + 1) * factorial n

-- Compute mode
#eval factorial 5  -- Outputs 120
#eval factorial 10 -- Outputs 3628800

-- n! ≈ Gamma(n+1)
-- Stirling's approximation of factorial
def ffactorial (x : Float) : Float :=
  x ^ x * Float.exp (-x) * Float.sqrt (tau * x) -- Stirling's approximation, off by ≈1%

#eval ffactorial 5.0 -- Outputs 118.019
#eval (ffactorial 10.0).toUInt64 -- 3598695 ≈ 3628800
-- #eval (ffactorial 10.0).toNat -- 3598695 ≈ 3628800

-- Iterative factorial function for non-integer Float values
def fac_iter (n : Float) : Float :=
  let rec loop (acc : Float) (i : Float) : Float :=
    if i > n then acc
    else loop (acc * i) (i + 1.0)
  if n < 1.0 then 1.0
  else loop 1.0 1.0
  termination_by n - i

#eval fac_iter 5.0


def factorian : ℕ → ℝ
| (0 : Nat)      => 1
| (n + 1) => (n + 1 : ℝ) * factorial n

-- def factoreal : ℝ → ℝ  unsalvageable!
-- | 0 => 1
-- | (n + 1) => (n + 1) * factorial n
-- invalid patterns, `n` is an explicit pattern variable, but it only occurs in positions that are inaccessible to pattern matching .(Real.add✝ n 1)

open Real
noncomputable
def factoreal (x : ℝ) : ℝ :=  -- via gamma_approx
  x ^ x * exp (-x) * sqrt (2 * π * x) -- Stirling's approximation

theorem factorial_pos (n : Nat) (h : n > 0) : factorial n > 0 :=
  match n, h with
  | 0, h => False.elim (Nat.not_succ_le_zero 0 h)
  | n+1, _ =>
    by
      show (n + 1) * factorial n > 0
      apply Nat.mul_pos
      apply Nat.succ_pos
      apply factorial_pos n -- induction hypothesis, assumes factorial n is positive for n
      -- exact factorial_pos n (Nat.lt_trans (Nat.zero_lt_succ n) h)


-- Proof mode
theorem factorial_nonzero (n : ℕ) : factorial n ≠ 0 := by
  induction n with d hd,
  -- base case
  simp [factorial],  -- Compute mode simplification within proof mode
  -- inductive step
  simp [factorial],  -- Simplify factorial definition
  apply mul_ne_zero,
  linarith,          -- `linarith` tactic proves non-zero property based on linear arithmetic
  exact hd,

-- theorem factorial_pos2 : ∀ (n : Nat), n > 0 → factorial n > 0 := by
--   intro n
--   cases n with
--   | zero => intro h; contradiction
--   | succ n =>
--     intro h
--     calc
--       factorial (n.succ) = (n.succ) * factorial n  : by rfl
--                      _ > 0 * factorial n         : by
--                      apply Nat.mul_pos; exact Nat.succ_pos n; apply factorial_pos n; exact Nat.succ_pos n



-- Stirling's approximation of factorial using floating-point arithmetic
def fac (n : Float) : Float :=
  if n ≥ 1.0 then
    Float.exp (n * Float.log n - n + 1.0)
  else
    0.0




noncomputable def fac (n : ℝ) : ℝ :=
  if h : n ≥ 1 then
    Real.exp (n * Real.log n - n + 1)
  else
    0

#eval fac 5
