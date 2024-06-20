-- import data.real.basic -- Import basic real number theory in LEAN 3
import Mathlib.Data.Real.Basic -- Import basic real number theory in LEAN 4
import Mathlib.Data.Real.Ereal -- ∞
-- import Mathlib.Data.Real.Hyperreal -- defined as hyperfilter germ
-- import Init.Data.Nat.Basic
-- import Init.Prelude
-- import Init.Control.Basic -- Import basic control structures in LEAN 4

-- def Hyperreal : Type := Germ (hyperfilter ℕ : Filter ℕ) ℝ deriving Inhabited
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


instance : Coe Bool ℕ where
  coe r := if r then 1 else 0

instance : Coe Bool ℚ where
  coe r := if r then 1 else 0

-- instance : HMul ℚ Bool ℚ where -- needed!
--   hMul q f := fun x => q * (f.toNat:ℚ)


-- scope Pair
namespace Pair
-- "'LT' has already been declared"

-- automatically generates GT. EQ implicit??
instance LT : LT (ℕ × ℕ) where
  lt f g := f.1 < g.1 ∨ (f.1 = g.1 ∧ f.2 < g.2)

-- this is silly, we provide a proof that the ordering is decidable
-- when it is obviously decidable because we gave a calcualble definition
-- Since both  <  and  =  on  ℕ  are already decidable, the compound relation  f.1 < g.1 ∨ (f.1 = g.1 ∧ f.2 < g.2)  is automatically decidable by the properties of  <  and  =  on natural numbers.
instance : DecidableRel (LT.lt : ℕ × ℕ → ℕ × ℕ → Prop) :=
-- (a b : α) → Decidable (r a b)
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



#eval (1, 2) < (2, 1)
#eval (2, 2) < (2, 2)
#eval (2, 2) <= (2, 2)
#eval (2, 1) < (2, 1)
#eval (2, 1) > (2, 1)
#eval (2, 1) >= (2, 1)
#eval (2, 1) = (2, 1)

end Pair
