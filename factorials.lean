
def fibonacci : Nat → Nat
| 0 => 0
| 1 => 1
| (n + 2) => fibonacci (n + 1) + fibonacci n

theorem fibonacci_nonneg (n : Nat) : fibonacci n ≥ 0 :=
  match n with
  | 0 => Nat.zero_le 0
  | 1 => Nat.zero_le 1
  | n + 2 => Nat.add_nonneg (fibonacci_nonneg (n + 1)) (fibonacci_nonneg n) -- recursive proof!

def factorial : ℕ → ℕ
| 0 => 1
| (n + 1) => (n + 1) * factorial n

-- Compute mode
#eval factorial 5  -- Outputs 120

theorem factorial_pos (n : Nat) (h : n > 0) : factorial n > 0 :=
  match n, h with
  | 0, h => False.elim (Nat.not_succ_le_zero 0 h)
  | n+1, _ =>
    by
      show (n + 1) * factorial n > 0
      apply Nat.mul_pos
      apply Nat.succ_pos
      exact factorial_pos n (Nat.lt_trans (Nat.zero_lt_succ n) h)


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

theorem factorial_pos : ∀ (n : Nat), n > 0 → factorial n > 0 := by
  intro n
  cases n with
  | zero => intro h; contradiction
  | succ n =>
    intro h
    calc
      factorial (n.succ) = (n.succ) * factorial n  : by rfl
                     _ > 0 * factorial n         : by
                     apply Nat.mul_pos; exact Nat.succ_pos n; apply factorial_pos n; exact Nat.succ_pos n
