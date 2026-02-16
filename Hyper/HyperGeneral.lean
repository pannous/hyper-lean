-- import data.real.basic -- Import basic real number theory in LEAN 3
import Mathlib.Data.Real.Basic -- Import basic real number theory in LEAN 4
-- import Mathlib.Data.Real.Ereal -- ∞
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
notation "𝔽" => ℚ -- our field, true alias
-- def 𝔽 := ℚ -- treats it as own Type!!
-- variable {𝔽 : Type*} [field 𝔽] -- “Let 𝔽 be a field.”

def Comps := List (𝔽 × 𝔽)
-- def Comps := List (ℝ × ℝ)
-- def Comps := List (ℝ × ℚ) -- what about ε^π :) seriously, needed in e^πi = -1
-- def Comps := List (ℝ × ℤ) -- ℤ for exponents integer powers of ε and ω enough for now
-- def Comps := List (ℚ × ℚ)  -- but what about π?

-- def HyperGeneral : Type := List (𝔽 × 𝔽)

structure HyperGeneral :=
  components : List (𝔽 × 𝔽)

notation "R*" => HyperGeneral
-- notation "ℚ*" => R* -- but what about π?
notation "𝔽*" => R*
notation "𝔽⋆" => R*
-- notation "ℝ⋆" => R* -- may conflict with Hyper from Hyper.lean
-- notation "ℝ*" => R* -- may conflict with Lean 4 notation for hyperreals

-- def Hyper:= R* -- remove!

  -- components : 𝔽 → 𝔽 -- as Function, see HyperFun
  -- components : List (ℝ × ℝ) -- allow π√ε
  -- components : List (ℚ × ℚ) -- allow π√ε approximation for now
  -- components : List (Float × Float) -- allow π√ε approximation for now
  -- components : List (ℝ × ℤ) -- [(3, 0), (1, 1), (2, -2)] => 3 + ω + 2ε^2 -- note ε = ω⁻¹
  -- components : ℤ → ℝ  -- generalized for infinite lists of components
  -- components : Comps -- with indirection we can't use add := λ x y => ⟨x.components ++ … why?

-- structure HyperSimple :=
  -- components : ℝ × ℤ  -- ONE of (3, 0), (1, 1), (2, -2) … => 3 or ω or 2ε^2 -- note ε = ω⁻¹
  -- components : ℝ × ℝ  -- ONE of (3, 0), (1, 1), (2, -2) … => 3 or ω or 2ε^2 -- note ε = ω⁻¹

structure HyperExtension (α : Type*) extends Real :=
  (infinite : α)


instance : One R* where
  one := ⟨[(1, 0)]⟩

instance : Zero R* where
  zero := ⟨[]⟩

instance : Inhabited R* where
  default := {
    components := []
  }

def zero : R* := ⟨[]⟩
def one : R* := ⟨[(1, 0)]⟩
def epsilon : R* := ⟨[(1, -1)]⟩
def omega : R* := ⟨[(1, 1)]⟩

-- scoped notation "0" => zero -- doesn't work "invalid atom" also NOT NEEDED! use 0 or 0 : 𝔽*
scoped notation "O" => zero
scoped notation "I" => one
scoped notation "ε" => epsilon
scoped notation "ω" => omega

instance : Coe ℕ 𝔽* where
  coe (n:ℕ) : R* := ⟨[((n:𝔽), 0)]⟩

instance {n : ℕ} : OfNat R* n where
  ofNat := ⟨[(n, 0)]⟩

instance : Coe ℚ 𝔽* where
  coe (q:ℚ) : R* := ⟨[(q, 0)]⟩

instance : Add R* where
  add x y := ⟨x.components ++ y.components⟩ -- unordered list :(

instance : Mul R* where
  mul x y := ⟨(x.components.product y.components).map (λ ⟨(r1, e1), (r2, e2)⟩ => (r1 * r2, e1 + e2))⟩

instance : Neg R* where
  neg x := ⟨x.components.map (λ ⟨r, e⟩ => (-r, e))⟩

instance : Sub R* where sub x y := x + -y

instance : HSMul 𝔽 R* R* where
  hSMul r a := ⟨(a.components.map (λ ⟨s, e⟩ => ((r * s), e)))⟩

instance : HSMul ℕ R* R* where
  hSMul r a := ⟨(a.components.map (λ ⟨s, e⟩ => ((r * s), e)))⟩

instance : Inv R* where
  inv x := ⟨x.components.map (λ ⟨r, e⟩ => (r⁻¹, -e))⟩

instance : SMul ℤ R* where
  smul n x := ⟨x.components.map (λ ⟨r, e⟩ => (n * r, e))⟩

#eval  ω * ε -- [(1, 0)] OK
#eval  2*ω * ε -- [(1, 0)] OK

-- 1 + 2ω + 1 + 2ω  ≈ ([1,0],[2,1],[1,0],[2,1]]) => ([2,0],[4,1)) ≈ 2 + 4ω
def simplify (a:R*) : R* :=
  ⟨a.components.foldl (λ acc x => acc ++ [x]) []⟩

#eval simplify (1:𝔽*) + ω + 1 + ε -- 2 + 4ω
-- #eval simplify (1:𝔽*) + 2*ω + 1 + 2*ω -- 2 + 4ω

instance : Field R* := {
  add := λ x y => ⟨x.components ++ y.components⟩,
  neg := λ x => ⟨x.components.map (λ ⟨r, e⟩ => (-r, e))⟩,
  inv := λ x => ⟨x.components.map (λ ⟨r, e⟩ => (r⁻¹, -e))⟩,
  zero := zero,
  one := one,
  mul := λ x y =>
    ⟨(x.components.product y.components).map (λ ⟨(r1, e1), (r2, e2)⟩ => (r1 * r2, e1 + e2))⟩,
  div := λ x y => x * y⁻¹,
  npow := λ n x => ⟨x.components.map (λ ⟨r, e⟩ => (r^n, e*n))⟩,
  nsmul := λ n x => ⟨x.components.map (λ ⟨r, e⟩ => (n * r, e))⟩,
  qsmul := λ q x => ⟨x.components.map (λ ⟨r, e⟩ => (q * r, e))⟩,
  nnqsmul := λ q x => ⟨x.components.map (λ ⟨r, e⟩ => (q * r, e))⟩,
  zsmul := λ n x => ⟨x.components.map (λ ⟨r, e⟩ => (n * r, e))⟩,
  zsmul_zero' := fun x => by sorry,
  zsmul_succ' := fun n x => by sorry,
  zsmul_neg' := fun n x => by sorry,
  -- gsmul := λ n x => ⟨x.components.map (λ ⟨r, e⟩ => (n * r, e))⟩,
  add_assoc := by
    intros a b c
    have h : (a.components ++ b.components) ++ c.components = a.components ++ (b.components ++ c.components) :=
      List.append_assoc a.components b.components c.components
    exact congrArg HyperGeneral.mk h
  zero_add := by
    intros a
    rfl,
  add_zero := by
    intros a
    sorry
  add_comm := by
    intros a b
    sorry,
  -- add_left_neg := by
  --   intros a
  --   simp only [List.map_map]
  --   -- Simplification would require a proper grouping function.
  --   sorry,
  mul_assoc := by
    intros a b c
    sorry,
  one_mul := by
    intros a
    sorry,
  mul_one := by
    intros a
    sorry,
  left_distrib := by
    intros a b c
    sorry,
  right_distrib := by
    intros a b c
    sorry,
  mul_comm := by
    intros a b
    sorry,
  mul_inv_cancel := by
    intros a ha
    -- Need to define a simplification that cancels inverses in our structure.
    sorry,
  -- inv_mul_cancel := by
  --   intros a ha
  --   -- Same issue as above, requires simplification function.
  --   sorry,
  -- zero_ne_one := by
  --   intro h
  --   -- This would require proving that `[] ≠ [(1,0)]` which is trivial but needs explicit `List` reasoning.
  --   sorry

--   -- include proofs showing these satisfy field axioms
--   zero_add := sorry,
  zero_mul := sorry,
  mul_zero:=sorry,
  exists_pair_ne := sorry,
  inv_zero:=sorry,
  neg_add_cancel:=sorry,
  nsmul_zero:= sorry,
  nsmul_succ:=sorry,
  npow_zero:=sorry,
  npow_succ:=sorry,
  nnqsmul_def:=sorry,
  qsmul_def:=sorry,
  -- zsmul_def:=sorry,
  -- zsmul_zero:=sorry,
  -- by
  --   intros x
  --   rw [List.append_nil]
  --   rfl,
  -- nsmul_zero1 := by
  --   intros x
  --   rw [List.map_nil, List.nil_append]
  --   rfl,
--   add_assoc := sorry,
--   add_zero := sorry,
--   add_comm:=sorry,
--   -- add_left_neg:=sorry,
--   left_distrib:=sorry,
--   right_distrib:=sorry,
--   one_mul:=sorry,
--   mul_assoc:=sorry,
--   mul_one:=sorry,
--   mul_inv_cancel:=sorry,
--   mul_comm:=sorry,
--   zsmul:=sorry,

  -- zsmul_zero:=sorry,
  -- zsmul_succ:=sorry,
  -- gsmul := sorry,
  -- nsmul:=sorry,
-- by
--   intros n x
--   rw [List.map_map]
--   simplify,
  -- npow_succ:=sorry,
  -- npow_zero:=sorry,
  -- nsmul_succ:=sorry,
  -- zsmul_neg:=sorry,
  -- zsmul_zero:=sorry,
  -- zsmul_succ:=sorry,
  -- gsmul := sorry,
--   nsmul:=sorry,
}


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
