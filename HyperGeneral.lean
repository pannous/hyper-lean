-- import data.real.basic -- Import basic real number theory in LEAN 3
import Mathlib.Data.Real.Basic -- Import basic real number theory in LEAN 4
import Mathlib.Data.Real.Ereal -- ∞
import Mathlib.Data.Real.Hyperreal -- defined as hyperfilter germ
import Init.Data.Nat.Basic
import Init.Prelude
import Init.Control.Basic -- Import basic control structures in LEAN 4

-- def Hyperreal : Type := Germ (hyperfilter ℕ : Filter ℕ) ℝ deriving Inhabited
notation "∞" => (⊤ : EReal)
notation "-∞" => (⊥ : EReal)

-- scoped notation "ε" => epsilon
-- scoped notation "ω" => omega

namespace Hypers
section HyperGenerals

-- Avoid Real Numbers When Possible:
-- If the use of real numbers introduces complexity due to issues like non-decidability of equality, consider if your application can tolerate using rational numbers or fixed-point arithmetic, which do not have these issues in Lean.

def Comps := List (ℝ × ℝ)
-- def Comps := List (ℝ × ℚ) -- what about ε^π :) seriously, needed in e^πi = -1
-- def Comps := List (ℝ × ℤ) -- ℤ for exponents integer powers of ε and ω enough for now
-- def Comps := List (ℚ × ℚ)  -- but what about π?

structure HyperGeneral :=
  components : List (ℝ × ℤ) -- [(3, 0), (1, 1), (2, -2)] => 3 + ω + 2ε^2 -- note ε = ω⁻¹
  -- components : ℤ → ℝ  -- generalized for infinite lists of components
  -- components : Comps -- with indirection we can't use add := λ x y => ⟨x.components ++ … why?

structure HyperSimple :=
  components : ℝ × ℤ  -- ONE of (3, 0), (1, 1), (2, -2) … => 3 or ω or 2ε^2 -- note ε = ω⁻¹
  -- components : ℝ × ℝ  -- ONE of (3, 0), (1, 1), (2, -2) … => 3 or ω or 2ε^2 -- note ε = ω⁻¹

structure HyperExtension (α : Type*) extends Real :=
  (infinite : α)

-- notation "ℚ*" => HyperGeneral -- but what about π?
notation "ℝ⋆" => HyperGeneral -- may conflict with Hyper from Hyper.lean
notation "ℝ*" => HyperGeneral -- may conflict with Lean 4 notation for hyperreals

instance : One HyperGeneral where
  one := ⟨[(1, 0)]⟩

instance : Zero HyperGeneral where
  zero := ⟨[]⟩

instance : Inhabited HyperGeneral where
  default := {
    components := []
  }

def zero : HyperGeneral := ⟨[]⟩
def one : HyperGeneral := ⟨[(1, 0)]⟩
def epsilon : HyperGeneral := ⟨[(1, -1)]⟩
def omega : HyperGeneral := ⟨[(1, 1)]⟩

-- scoped notation "0" => zero -- doesn't work "invalid atom"
scoped notation "O" => zero
scoped notation "I" => one
scoped notation "ε" => epsilon
scoped notation "ω" => omega

-- coercion from reals to hyperreals
instance : Coe ℝ ℝ⋆ where
  coe r := HyperGeneral.mk [(r,0)]

-- This instance already exists in Lean’s standard library, so you don’t need to redefine it.
-- instance : Coe ℕ ℝ⋆ where
  -- coe n := Nat.cast n --n.toReal
instance : Coe ℕ ℝ⋆ where
  coe (n:ℕ) : HyperGeneral := ⟨[( (n:ℝ), 0)]⟩
  instance : Coe ℕ ℝ⋆ where
  coe (n:ℕ) : HyperGeneral := ⟨[( (n:ℝ), 0)]⟩


-- instance : Field HyperGeneral := {
--   mul := λ x y => HyperGeneral.mk (
--     List.bind x.components (λ px =>
--       y.components.map (λ py => (px.1 * py.1, px.2 + py.2)))
--   ),
--   -- add := λ x y => HyperGeneral.mk ( x.components ++ y.components ),
--   add := λ x y => ⟨x.components ++ y.components⟩,
--   neg := λ x => ⟨x.components.map (λ ⟨r, e⟩ => (-r, e))⟩,
--   inv := λ x => ⟨x.components.map (λ ⟨r, e⟩ => (r⁻¹, -e))⟩,
--   zero := zero,
--   one := one,
--   -- include proofs showing these satisfy field axioms
--   zero_add := sorry,
--   zero_mul := sorry,
--   add_assoc := sorry,
--   add_zero := sorry,
--   add_comm:=sorry,
--   add_left_neg:=sorry,
--   left_distrib:=sorry,
--   right_distrib:=sorry,
--   one_mul:=sorry,
--   mul_zero:=sorry,
--   mul_assoc:=sorry,
--   mul_one:=sorry,
--   mul_inv_cancel:=sorry,
--   mul_comm:=sorry,
--   zsmul:=sorry,
--   qsmul:=sorry,
--   exists_pair_ne:=sorry,
--   inv_zero:=sorry,
--   nnqsmul:=sorry,
--   nsmul:=sorry,
-- }


  -- inv_zero:= sorry,
  -- zero_add := λ x => sorry,
  -- zero_mul := λ x => sorry,
  -- add_assoc := λ x y => sorry,
  -- add_zero := λ x => sorry,
  -- add_comm:= λ x y => sorry,
  -- add_left_neg:= λ x => sorry,
  -- left_distrib:= λ x y => sorry,
  -- right_distrib:= λ x y => sorry,
  -- one_mul:=λ x => sorry,
  -- mul_zero:= λ x => sorry,
  -- mul_assoc:= λ x y => sorry,
  -- mul_one:= λ x => sorry,
  -- mul_inv_cancel:= λ x y => sorry,
  -- mul_comm:= λ x y => sorry,
  -- zsmul:= λ x y => sorry,
  -- qsmul:= λ x y => sorry,
  -- exists_pair_ne:= sorry,
  -- nnqsmul:= λ x y => sorry,
  -- nsmul:= λ x y => sorry,

end HyperGenerals
end Hypers
