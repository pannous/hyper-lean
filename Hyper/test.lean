import Mathlib.Data.Real.Basic
import Mathlib.Tactic
example {a b : ℤ} : (a - b) * (a + b) = a^2 - b^2 := by
  calc
    (a - b) * (a + b) = a^2 - a*b + a*b - b^2 := by ring
    _ = a^2 - b^2 := by ring

def main : IO Unit :=
  IO.println "Hello, World!"

def addOne (n : Nat) : Nat := n + 1

theorem addOne_correct (n : Nat) : addOne n = n + 1 := by
  rfl

theorem add_zero (n : Nat) : n + 0 = n := by
  rfl

theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.add_succ]
    rw [ih]

-- set_option diagnostics true
-- def addOner (x : ℝ) : ℝ := x + (1 : ℝ)

-- theorem addOner_correct (x : ℝ) : addOner x = x + (1 : ℝ) := by
--   rfl

#eval main
#eval addOne 5  -- This will output 6
