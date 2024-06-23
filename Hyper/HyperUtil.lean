import Mathlib.Data.Real.Basic -- Import basic real number theory in LEAN 4
import Mathlib.Data.Real.Ereal -- ∞

variable {T : Type} [DecidableEq T] [LT T] [DecidableRel (LT.lt : T → T → Prop)]
variable {S : Type} [DecidableEq S] [LT S] [DecidableRel (LT.lt : S → S → Prop)]

-- Define the less-than relation for pairs (lexicographic order)
instance : LT (T × S) where
  lt := λ a b => a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)

instance genericPairsDecidableRel: DecidableRel (LT.lt : T × S → T × S → Prop) :=
  fun (a,b) (c,d) =>
    if h₁ : a < c then isTrue (Or.inl h₁)
    else if h₂ : a = c then
      if h₃ : b < d then
        isTrue (Or.inr ⟨h₂, h₃⟩)
      -- the rest is even more silly since we have to turn everything around
      else isFalse (λ (h : a < c ∨ (a = c ∧ b < d)) =>
        Or.elim h
        (λ hlt : a < c => absurd hlt h₁)
        (λ heq : a = c ∧ b < d =>
        absurd (And.right heq) h₃))
    else isFalse (λ (h : a < c ∨ (a = c ∧ b < d)) =>
        Or.elim h
        (λ hlt : a < c => absurd hlt h₁)
        (λ heq : a = c ∧ b < d =>
          absurd (And.left heq) h₂)
          )

-- def coerce_pair (p : ℕ × ℕ) : ℤ × ℤ := (p.1, p.2)

-- example : Decidable ((3, 4) < (3, 5) : ℤ × ℤ → ℤ × ℤ → Prop) := genericPairsDecidableRel -- Should succeed
-- example : (3, 4) < (3, 5)  := by exact genericPairsDecidableRel -- Should succeed

-- instance : DecidableRel (LT.lt : ℕ × ℕ → ℕ × ℕ → Prop) := genericPairsDecidableRel
-- ⅟ ½ ⅓ ⅔ ¼ ¾ ⅕ ⅖ ⅗ ⅘ ⅙ ⅚ ⅐ ⅛ ⅜ ⅝ ⅞
-- notation "⅟" x := (1 / x)
-- def half: ℚ := 1 / 2
-- notation "½" => half
prefix:10 "⅟" => fun x => 1 / x
-- #eval ⅟2.

-- ⁻¹ ⁰ ¹ ² ³ ⁴ ⁵ ⁶ ⁷ ⁸ ⁹

notation "½" => (1 / 2 : ℚ)
notation "⅓" => (1 / 3 : ℚ)
notation "⅔" => (2 / 3 : ℚ)
notation "¼" => (1 / 4 : ℚ)
notation "¾" => (3 / 4 : ℚ)
notation "⅕" => (1 / 5 : ℚ)
notation "⅖" => (2 / 5 : ℚ)
notation "⅗" => (3 / 5 : ℚ)
notation "⅘" => (4 / 5 : ℚ)
notation "⅙" => (1 / 6 : ℚ)
notation "⅚" => (5 / 6 : ℚ)
notation "⅐" => (1 / 7 : ℚ)
notation "⅛" => (1 / 8 : ℚ)
notation "⅜" => (3 / 8 : ℚ)
notation "⅝" => (5 / 8 : ℚ)
notation "⅞" => (7 / 8 : ℚ)

-- #eval ½+⅕

-- #eval ½+½+½
-- #eval 2+½
-- #eval 2*½
-- #eval (-1, -2) < (2, 1)
-- #eval (½, 2) < (2, 1)
-- #eval (2, 2) < (2, 2)
-- #eval (2, 2) <= (2, 2)
-- #eval (2, 1) < (2, 1)
-- #eval (2, 1) > (2, 1)
-- #eval (2, 1) >= (2, 1)
-- #eval (2, 1) = (2, 1)

-- end Pair

notation "∞" => (⊤ : EReal)
notation "-∞" => (⊥ : EReal)

def square {α : Type*} [Mul α] (x : α) : α := x * x
def inv_square {α : Type*} [Inv α] [Mul α]  (x : α) : α := (x * x)⁻¹

instance : Inv Float where
  inv := fun x => 1 / x

notation x "²" => square x
notation x "⁻²" => inv_square x


instance : ToString ℚ where
  toString q :=
    if q.den = 1 then
      toString q.num  -- Just show the numerator if the denominator is 1
    else
      toString q.num ++ "/" ++ toString q.den

instance : ToString Bool where
  toString ja :=
    if ja then "true" else "false"
