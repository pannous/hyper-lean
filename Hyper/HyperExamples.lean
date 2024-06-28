import Hyper
-- two instances of the same type are the same if their components are the same
example : Hyper.mk 1 2 3 = Hyper.mk 1 2 3 := by
  rfl

example : Hyper.mk 1 2 3 = Hyper.mk 1 2 (2 + 1) := by
  apply Hyper.ext
  rfl  -- real_part is directly equal
  rfl  -- epsilon_part is directly equal
  norm_num

example : Hyper.mk 1 2 3 = Hyper.mk 1 2 (2 + 1) := by
  -- congruence very powerful!
  congr -- when f x = f y and you want to reduce it to x = y, here we have f = Hyper.mk
  norm_num

def h1 := Hyper.mk 1 2 3
def h2 := Hyper.mk 4 5 6


example : h1 + h2 = Hyper.mk 5 7 9 := by
  let lhs := h1 + h2
  let rhs := Hyper.mk 5 7 9
  have h_real_part : lhs.real_part = rhs.real_part := by
    show 1 + 4 = 5;
    norm_num
  have h_epsilon_part : lhs.epsilon_part = rhs.epsilon_part := by
    show 2 + 5 = 7
    norm_num
  have h_infinite_part : lhs.infinite_part = rhs.infinite_part := by
    show 3 + 6 = 9
    norm_num
  apply Hyper.ext
  exact h_real_part
  exact h_epsilon_part
  exact h_infinite_part
-- NOT NEEDED / WORKING:
--   cases h1,
--   cases h2,
-- intro h
-- cases h
-- split
-- all_goals { rfl }
--   simp only [Add.add, Hyper.add]
-- congr use when f x = f y and you want to reduce it to x = y, here we have f = Hyper.mk


-- lemma hyper_addition :
-- lemma hyper_addition (a b c d e f : ℕ) : auto coerced to:
lemma hyper_addition (a b c d e f : ℝ) :
  Hyper.mk a b c + Hyper.mk d e f = Hyper.mk (a + d) (b + e) (c + f) := by
  let lhs := Hyper.mk a b c + Hyper.mk d e f
  let rhs := Hyper.mk (a + d) (b + e) (c + f)
  have h_real_part : lhs.real_part = rhs.real_part := by
    show a + d = a + d
    norm_num
  have h_epsilon_part : lhs.epsilon_part = rhs.epsilon_part := by
    show b + e = b + e
    norm_num
  have h_infinite_part : lhs.infinite_part = rhs.infinite_part := by
    show c + f = c + f
    norm_num
  apply Hyper.ext
  exact h_real_part
  exact h_epsilon_part
  exact h_infinite_part

-- apply the lemma to prove an addition
example : Hyper.mk 1 2 3 + Hyper.mk 4 5 6 = Hyper.mk (1 + 4) (2 + 5) (3 + 6) := by
  apply hyper_addition

-- example : h1 + h2 = Hyper.mk 5 7 9 := by
--   apply hyper_addition -- CAN'T DO THIS

-- example : h1 + h2 = Hyper.mk 5 7 9 := by
--   have h := hyper_addition 1 2 3 4 5 6
--   rw [h] -- Can't do this
--   norm_num



def h01 := Hyper.mk 1 0 0
def h02 := Hyper.mk 0 1 0

-- Example to verify multiplication
example : h01 * h02 = Hyper.mk 0 1 0 := by
  apply Hyper.ext
  {show 1 * 0 + 0 * 0 = 0; norm_num}
  {show 1 * 1 + 0 * 0 = 1; norm_num}
  {show 1 * 0 + 0 * 0 = 0; norm_num}


-- The expected result of multiplying h1 and h2
def expected := Hyper.mk (1*4 + 2*6) (1*5 + 2*4) (1*6 + 3*4)

def example_hyper_mul : ℝ⋆ :=
  let a := Hyper.mk 1 2 3
  let b := Hyper.mk 4 5 6
  a * b

-- example : example_hyper_mul = ⟨1 * 4 + 2 * 6, 1 * 5 + 2 * 4, 1 * 6 + 3 * 4⟩ := by
example : example_hyper_mul = expected := by
-- example : example_hyper_mul = ⟨16, 13, 18⟩ := by
  let lhs := example_hyper_mul
  let rhs : Hyper := ⟨1 * 4 + 2 * 6, 1 * 5 + 2 * 4, 1 * 6 + 3 * 4⟩
  have h_real_part : lhs.real_part = rhs.real_part := by
    show 1 * 4 + 2 * 6 = 1 * 4 + 2 * 6
    norm_num
  have h_epsilon_part : lhs.epsilon_part = rhs.epsilon_part := by
    show 1 * 5 + 2 * 4 = 1 * 5 + 2 * 4
    norm_num
  have h_infinite_part : lhs.infinite_part = rhs.infinite_part := by
    show 1 * 6 + 3 * 4 = 1 * 6 + 3 * 4
    norm_num
  apply Hyper.ext
  exact h_real_part
  exact h_epsilon_part
  exact h_infinite_part



lemma hyper_multiplication2 (a b c d e f) :
  (Hyper.mk a b c) * (Hyper.mk d e f) = Hyper.mk (a * d + b * f) (a * e + b * d) (a * f + c * d) := by
  apply Hyper.ext
  { show a * d + b * f = a * d + b * f; rfl } -- stupid show!
  { show a * e + b * d = a * e + b * d; rfl }
  { show a * f + c * d = a * f + c * d; rfl }


-- example : (↑(0:ℝ) : ℝ⋆) = (zero : ℝ⋆) := by


axiom epsilon_mul_omega_gauging : mul ε ω = one
-- axiom epsilon_mul_omega_gauging : ∀ (x : ℝ) , ( x ≠ 0 ) → (ε * ω = 1)
-- axiom epsilon_mul_omega_gauging : ∀ (ε ω : ℝ), (ε ≠ 0) → (ω ≠ 0) → (ε * ω = 1)


-- Define the standard part function
def standardPart (x : Hyper) : EReal :=
  if x.infinite_part==0 then x.real_part else if x.infinite_part > 0 then ∞ else -∞

-- lemmas about ε and ω
-- lemma ε_times_ω_equals_one : ε * ω = 1 := by
--   rw [Mul, ε, ω]
--   -- further simplifications and algebraic manipulation needed
--   sorry -- placeholder for proof


def main : IO UInt32 := do
  IO.println "Hello, tree!"
  pure 0

#eval main




-- Declare hyperreals as an extension of the reals
-- constant hyperreal : Type
-- constant ℝ* : Type
-- notation `ℝ*` := hyperreal
-- notation `ℝ*` := ℝ*

-- -- Declare infinitesimal and infinite numbers
-- constant epsilon : ℝ*
-- constant omega : ℝ*

-- -- Axioms for epsilon and omega
-- axiom epsilon_infinitesimal : ∀ r : ℝ, r > 0 → epsilon < r
-- axiom omega_infinite : ∀ r : ℝ, omega > r
-- axiom epsilon_omega_relation : epsilon * omega = 1

-- -- Additional axioms for ℝ*
-- -- Closure under ℝ operations
-- axiom add_closure : ∀ x y : ℝ*, x + y ∈ ℝ*
-- axiom mul_closure : ∀ x y : ℝ*, x * y ∈ ℝ*


-- -- transfer principle for hyperreals
-- axiom transfer : ∀ {P : ℝ → Prop}, (∀ r : ℝ, P r) → P epsilon → P omega → ∀ r : ℝ*, P r
