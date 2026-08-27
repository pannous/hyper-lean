#eval Lean.versionString

notation "ℕ" => Nat


-- computable def fac (n : ℕ) : ℕ :=
-- def fibonacci : Nat → Nat
def fibonacci : ℕ → ℕ
| 0 => 0
| 1 => 1
| (n + 2) => fibonacci (n + 1) + fibonacci n

#eval fibonacci 5


-- Prove that fibonacci 0 = 0
theorem fibonacci_zero : fibonacci 0 = 0 := rfl

-- Prove that fibonacci 1 = 1
theorem fibonacci_one : fibonacci 1 = 1 := rfl

-- Prove that fibonacci 2 = 1
theorem fibonacci_two : fibonacci 2 = 1 := rfl

-- Prove that fibonacci is increasing (fibonacci n ≤ fibonacci (n + 1))
theorem fibonacci_mono (n : ℕ) : fibonacci n ≤ fibonacci (n + 1) :=
  match n with
  | 0 => by simp [fibonacci]
  | 1 => by simp [fibonacci]
  | n + 2 => Nat.le_add_right _ _

-- Prove that fibonacci satisfies its recursive definition
theorem fibonacci_succ_succ (n : ℕ) : fibonacci (n + 2) = fibonacci (n + 1) + fibonacci n := rfl

-- Prove an explicit formula for small values
example : fibonacci 3 = 2 := rfl
example : fibonacci 4 = 3 := rfl
example : fibonacci 5 = 5 := rfl
example : fibonacci 6 = 8 := rfl
