import Mathlib.Topology.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.SetTheory.Surreal.Basic
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Linarith
-- import Mathlib.Data.Set.Univ
-- import Mathlib.Data.Set.Range

namespace Hypers
section HyperKeisler

-- set_option autoImplicit false -- to debug
-- set_option diagnostics true
-- set_option diagnostics.threshold 1000
-- set_option pp.all true
-- set_option checkBinderAnnotations false

-- ⚠️ Lean 4 DOES NOT CHECK SOUNDNESS OF AXIOMS ⚠️

-- [@implemented_by ] <<< only when executing code in Lean #eval, not in proofs
-- [@extern ...] fast C implementation
-- structure Hyperreal' := (real : ℝ) (epsilon : ℝ)
structure Hyperreal' where
  real : ℝ
  hype : ℝ -- not to be confused with hyper(ℝ) embedding

-- 	•	Use a class only if you need multiple models of hyperreals.
--  ℝ (for proofs) and Float (for computation).
axiom Hyperreal : Type -- e.g.
-- def Hyperreal := Hyperreal' -- Now they are the same

-- notation "Hyper" => Hyperreal
notation "𝔽" => ℚ -- our Field !
-- notation "𝔽" => ℝ -- our Field is ℝ ONLY IN Keisler!!
notation "R" => ℝ
-- notation "R" => R_subset -- alias dangerous??
notation "R*" => Hyperreal
notation "ℝ*" => Hyperreal
notation "R+" => { r : ℝ // r > 0 }
notation "ℝ+" => { r : ℝ // r > 0 }

-- axiom R_subtype : ℝ ⊂ ℝ*

--
-- put at the end of the file:
-- end Hyperreal

-- In mathematics, the system of hyperreal numbers is a way of treating infinite and infinitesimal (infinitely small but non-zero) quantities. The hyperreals, or nonstandard reals, *R, are an extension of the real numbers R with elements ω ≈ ∞ and ε ≈ 1/∞ and their algebraic span.
-- 0 < ε < r ∀r∊ℝ⁺

-- Axiom A
-- R is a complete ordered field (yes just the real numbers, we know them)


-- Axiom B: R* is an ordered field extension of R
-- Declare that Hyperreal is a linear ordered field
axiom LinearOrderedField_Hyperreal : LinearOrderedField R*

-- Register it as an instance (Lean allows us to defer the existence proof)
noncomputable instance : LinearOrderedField R* := LinearOrderedField_Hyperreal

-- The standard embedding ℝ → R* is a Ring Homomorphism
axiom hyper : ℝ →+* R* -- embedding constructor
-- constant (hyper : ℝ →+* R*) -- embedding constructor CAN BE DEFINED LATER!
-- def hyper : ℝ →+* R* :=
--   RingHom.mk (fun r => ⟨r, 0⟩) -- explicit embedding
--     (by simp)  -- map_one' -- prove it preserves 1
--     (by simp)  -- map_mul' -- prove it preserves multiplication
--     (by simp)  -- map_zero' -- prove it preserves 0
--     (by simp)  -- map_add' -- prove it preserves addition

-- axiom extension : ℝ → R*   -- without RingHom which we would have to add later

-- noncomputable instance : Ring R* := inferInstance -- Ring follows from LinearOrderedField
-- Ring Homomorphism / Field Homomorphism
-- axiom extension_hom : RingHom ℝ R* hyper
-- axiom extension_hom : FieldHom ℝ R* hyper

-- TODO we MAY make this all computable by giving a definition like
-- structure HyperGeneral :=
--   components : List (𝔽 × 𝔽)

-- Coerce real numbers into hyperreal numbers
-- Automatically infer Coe from RingHom
noncomputable instance : Coe ℝ R* := ⟨hyper⟩
noncomputable instance : Coe ℕ R* := ⟨λ n => hyper (n : ℝ)⟩
noncomputable instance : Coe ℤ R* := ⟨λ z => hyper (z : ℝ)⟩
noncomputable instance : Coe ℚ R* := ⟨λ q => hyper (q : ℝ)⟩
-- noncomputable instance : Coe ℝ R* := ⟨hyper.toFun⟩

-- Order compatibility with ℝ
axiom ordered_field_extension : ∀ (r s : ℝ), hyper r < hyper s ↔ r < s
theorem ordered_field_extension' : ∀ (r s : ℝ),  r > s ↔ hyper r > hyper s := by
    simp [ordered_field_extension]
-- theorem ordered_field_extension' : ∀ (r s : ℝ), hyper r > hyper s ↔ r > s := by
--     simp [ordered_field_extension]

-- theorem ordered_field_transfer (r : ℝ) (s : ℝ*) : r < s ↔ hyper r < s :=
--   ordered_field_extension r (coe s)

-- heterogeneous order relation or coercive order
-- apply '<' to ℝ and ℝ*  e.g. 0 < hyper 1 !
-- instance : StrictMono hyper := ordered_field_extension
-- instance : StrictMono R* := ⟨ hyper, ordered_field_extension ⟩
  -- { to_fun := hyper, monotone := ordered_field_transfer }

axiom ordered_field_transfer : ∀ (r : ℝ) , (s : ℝ*) → (r < s ↔ hyper r < s)
axiom ordered_field_reverse : ∀ (s : ℝ*) (r : ℝ), s < r ↔ s < hyper r
-- TODO: proof that these follow IF THEY DO:
-- axiom ordered_field_transfer_z : ∀ (r : ℝ) (s : ℝ*), (∃ z : ℝ*, z = hyper r) → (r < s ↔ z < s)
-- axiom ordered_field_transfer_z2 : ∀ (r : ℝ) (s : ℝ*) (z : ℝ*), z = hyper r → (r < s ↔ z < s)

-- axiom ordered_field_transfer_RR2 : ∀ (r s : ℝ) , r < s ↔ r < hyper s
theorem ordered_field_transfer_RR2 (r s : ℝ) : r < s ↔ r < hyper s :=
  (ordered_field_extension r s).symm.trans
    (ordered_field_transfer r (hyper s)).symm
#print axioms ordered_field_transfer_RR2

/--
From the coercion `Coe ℝ R* := ⟨hyper⟩`, `r < s` for `s : ℝ` implicitly means
`r < (s : R*) = hyper s`. Hence if `z = hyper s`, the two inequalities
`r < s` and `r < z` coincide definitionally.
-/
theorem ordered_field_transfer2 (r : R*) (s : ℝ) (z : R*) (hz : z = hyper s) : r < s ↔ r < z :=
  by rw [← hz]  -- both sides mean `r < hyper s`


-- Axiom C: Existence of a positive infinitesimal ε
axiom epsilon : R*

axiom epsilon_pos : 0 < epsilon
axiom epsilon_infinitesimal : ∀ r : ℝ, r > 0 → epsilon < hyper r
-- axiom epsilon_infinitesimal : ∀ r : ℝ+, epsilon < hyper r
-- axiom epsilon_infinitesimal' : ∀ r : ℝ, epsilon < |hyper r|
-- axiom epsilon_infinitesimal'' : ∀ r : ℝ, epsilon < hyper |r|

-- Extend the order: ℝ is naturally embedded in Hyperreal
axiom real_le_hyperreal : ∀ r : ℝ, ∀ x : R*, (r : R*) ≤ x ↔ (hyper r) ≤ x

-- Notation for R*ⁿ *Rⁿ Hyperreal vectors
notation "R*"n => (Fin n → R*) -- STILL needs to be wrapped as (R*n) WHY?
-- notation "R^"n => (Fin n → ℝ) ambiguous :
notation "ℝ^"n => (Fin n → ℝ)
-- notation "ℝⁿ" => Fin n → ℝ

-- Axiom D: Natural extension of functions
axiom D : ∀ {n : ℕ} (f : (ℝ^n) → ℝ),
  ∃ f_star : (R*n) → R*,
  ∀ (x : ℝ^n), f_star (hyper ∘ x) = hyper (f x)


-- Axiom E: Transfer principle
axiom E : ∀ (P : R* → Prop), (∀ r : ℝ, P (hyper r)) → (∀ x : R*, P x)


-- Definition 1.1: Infinitesimals, finites, and infinite elements
def finite  (x : R*) : Prop := ∃ r : ℝ, |x| < hyper r
def infinite  (x : R*) : Prop := ∀ r : ℝ, r > 0 → |x| > hyper r
def infinitesimal (x : R*) : Prop := ∀ r : ℝ, r > 0 → |x| < hyper r
-- def infinitesimal2 (x : R*) : Prop := ∀ r : R+, |x| < hyper r
-- lemma infinitesimal_iff_infinitesimal2 : infinitesimal x ↔ infinitesimal2 x :=
--   by simp [infinitesimal, infinitesimal2]

-- Type definitions as subtypes
def Finiteh : Type := {x : R* // finite x}
def Infiniteh : Type := {x : R* // infinite x}
def Infinitesimal : Type := {x : R* // infinitesimal x}

-- def Finites : Set R* := galaxy 0
def Finites : Set R* := {y | finite y} --  galaxy 0
def Infinitesimals : Set R* := {y | infinitesimal y} -- monad 0
def Infinites : Set R* := {y | infinite y} --

-- Hyperreal as a set! ⚠️ Hyperreal Type ≠ Hyperreals Set ⚠️ confusion!
def Hyperreals : Set R* := Set.univ  -- The set of all hyperreal numbers (trivial & redundant!)
def Reals : Set ℝ := Set.univ  -- ℝ as set (trivial & redundant!)
-- def R_subset : Set R* := {y | finite y ∧ ¬ infinitesimal y} -- ℝ embedded in R*
def R_subset : Set R* := Set.range hyper  -- ℝ embedded in R*
def R_subtype : Type := { x : R* // ∃ r : ℝ, x = hyper r }
def R_subtype' := { x : R* // x ∈ R_subset }

def Infinites' : Set R* := {y | ¬ finite y}  -- Equivalent to the complement of galaxy(0)
def Infinites'' : Set R* :=  Hyperreals \ Finites  -- Complement of the finite set
-- def Infinites : Set R* := Set.univ \ Finites  -- Complement of the finite set R*
-- Set R* represents the type of all subsets of  R^ *.
-- •	Set.univ is the universal set in Lean, meaning the set of all elements of  R^ *.


-- Theorem 1.9. (Standard Part Principle) Every finite x ∈R∗ is infinitely
-- close to a unique real number r ∈R. That is, every finite monad contains a
-- unique real number.


-- axiom st : R* → ℝ -- noncomputable and we can't make it computable later
axiom real : R* → ℝ -- noncomputable and we can't make it computable later
-- axiom real_part : R* → ℝ standard part
-- axiom hyper_part : R* → R* vs standard part
-- def real (x : R*) : ℝ := sorry -- Will be implemented later, e.g. :
-- def real (x : R*) : ℝ := x.real -- If implemented as a structure
-- def real : R* → ℝ
-- | epsilon => 0 -- "redundant"
-- | x       => x.real

-- structure Hyperreal' := (real : ℝ) (epsilon : ℝ)

class StandardPart (α : Type*) := (real : α → ℝ)

notation "st" => real -- alias st standard = real part of a hyperreal akin to `Re` in complex numbers
notation "standard" => real --  noncomputable def standard := real -- alias
axiom st_extension : ∀ r : ℝ, real (hyper r) = r
axiom extension_st : ∀ r : ℝ, hyper (real r) = r -- todo: as lemma
@[simp]
axiom pure_epsilon : real epsilon = 0  -- redundant but can't hurt
lemma pure_epsilon': real epsilon = 0  := by exact pure_epsilon -- simp [real] or pure_epsilon
#reduce real epsilon -- 0.0
-- noncomputable MTFK!!
-- #eval real epsilon -- 0.0

-- Add a "real" method to Hyperreal for accessing the standard part
-- @[inline] def Hyperreal.real (x : R*) : ℝ := real x -- already defined
-- #eval epsilon.real -- 0.0

lemma st_extension' (r : ℝ) : real (r : R*) = r := st_extension r -- via coercion

axiom st_reals : ∀ r : ℝ, real (hyper r) = r



def near (x y : R*) : Prop := infinitesimal (x - y)
def cofinite (x y : R*) : Prop := finite (x - y)
-- def near (x y : R*) : Prop := infinitesimal hyper (x - y)

-- Definition 1.2: Monad and Galaxy
def monad (x : R*) : Set R* := {y | near x y}
def galaxy (x : R*) : Set R* := {y | finite (x - y)}
-- def galaxy' (x : R*) : Set R* := {y | finite (y - x)}
-- def galaxy (x : R*) : Set R* := {y | cofinite (x y)}
def halo := monad -- alias


lemma hyper_zero : hyper 0 = (0 : R*) :=
  by exact hyper.map_zero

lemma zero_is_infinitesimal : infinitesimal (0 : R*) := by
  intro r hr
  -- By definition, "infinitesimal (0 : R*)" means ∀ r>0, |0| < hyper r
  simp only [infinitesimal, abs_zero]
  -- Show 0 < hyper r
  rw [← hyper_zero]      -- replace 0 with hyper 0
  exact (ordered_field_extension 0 r).mpr hr


-- Notation for near (≈)
-- notation x " ≈ " y => (near x y)
-- #print notation =  => 50, use that same precedence
-- BUILTIN infix:50 " == " => BEq
-- BUILTIN infix:50 " ≈ " => Equiv : near
infix:50 " ∻ " => cofinite -- ∺ within same galaxy 🌌

instance : HasEquiv R* where Equiv x y := near x y

-- def infinitesimal (x : R*) : Prop := ∀ r : ℝ, r > 0 → |x| < hyper r
lemma infinitesimal_abs (x : R*) : infinitesimal x = infinitesimal (-x) := by
  simp [infinitesimal, infinitesimal, abs_neg]

lemma infinitesimal_epsilon : infinitesimal epsilon := by
  have epsilon_abs : |epsilon| = epsilon  := abs_of_pos epsilon_pos
  rw [infinitesimal, epsilon_abs]
  exact epsilon_infinitesimal

lemma zero_near_epsilon : (0 : R*) ≈ epsilon := by
  show infinitesimal (0 - epsilon)
  simp only [zero_sub]
  show infinitesimal (-epsilon)
  rw [infinitesimal_abs]
  simp
  show infinitesimal (epsilon)
  exact infinitesimal_epsilon

lemma zero_is_infinitesimal' : infinitesimal (0 : R*) := by
  intro r hr
  -- By definition, "infinitesimal (0 : R*)" means ∀ r>0, |0| < hyper r
  simp only [infinitesimal, abs_zero]
  -- Show 0 < hyper r
  rw [← hyper_zero]      -- replace 0 with hyper 0
  exact (ordered_field_extension 0 r).mpr hr

lemma zero_near_zero : (0 : R*) ≈ 0 := by
  show infinitesimal (0 - 0)
  simp only [sub_self]
  exact zero_is_infinitesimal'

-- example : zero ≈ epsilon := by simp
-- Coercion from R to R* works
example (r : ℝ) (x : R*) : r + x = hyper r + x := rfl
example (r : ℝ) : r = hyper r := rfl

noncomputable def st_R_subset : R_subset → ℝ := λ x => real x -- standard part of x in R_subset
noncomputable def st_R_subtype : R_subtype → ℝ := λ s => real s.val -- wth is s.val? egal ;)
noncomputable def st_R_subtype' : R_subtype' → ℝ := λ s => real s.val

lemma st_is_inverse (x : R*) (h : x ∈ R_subset) : hyper (real x) = x := by
  obtain ⟨r, hr⟩ := h -- x = hyper r for some r ∈ ℝ
  have h0 : hyper r = x := hr
  have h1 : real x = r := by rw [←h0, st_extension]
  rw [h1]
  exact hr

-- lemma st_is_inverse_back (x : 𝔽) : real (hyper x) = x := st_extension x
@[simp]
lemma st_hyper_is_id (x : R) : real (hyper x) = x := st_extension x

@[simp]
lemma st_is_inverse' (x : R*) (h : x = hyper r) : hyper (real x) = x := by
  obtain ⟨r, hr⟩ := h -- x = hyper r for some r ∈ ℝ
  have h: real (hyper r) = r := st_extension r
  rw [h]

noncomputable def R_subtype_equiv : ℝ ≃ R_subtype := {
  toFun := λ r => ⟨hyper r, ⟨r, rfl⟩⟩,
  invFun := λ s => real s.val,
  left_inv := λ r => by simp only; exact st_hyper_is_id (r),
  right_inv := λ ⟨x, ⟨r, hr⟩⟩ => by
    apply Subtype.ext
    simp [st_is_inverse]
    exact st_is_inverse' x hr
}

-- @[simps apply] -- ≃ Equiv Equivalence
noncomputable def R_subset_equivalent : ℝ ≃ R_subset := {
  toFun := λ r => ⟨hyper r, ⟨r, rfl⟩⟩, -- 𝞅
  invFun := st_R_subset, -- 𝞅⁻¹
  left_inv := λ r => by simp [st_R_subset, st_extension], -- 𝞅⁻¹•𝞅=1
  right_inv := λ ⟨x, ⟨r, hr⟩⟩ => by -- 𝞅•𝞅⁻¹=1
    show (⟨hyper (real x), ⟨real x, rfl⟩⟩ : R_subset) = ⟨x, ⟨r, hr⟩⟩
    apply Subtype.ext
    show hyper (real x) = x
    rw [← hr, extension_st]
}



instance : Coe R+ ℝ := ⟨Subtype.val⟩ -- coercion from R+ to ℝ
instance : Coe R_subtype ℝ* := ⟨Subtype.val⟩ -- coercion from R to R*  ( R ≃ ℝ )


lemma hyper_keeps_sign (r : ℝ) : r > 0 ↔ hyper r > hyper 0 := by
  exact ordered_field_extension' r 0


-- macro "later" : tactic => `(tactic| exact sorry)
macro "later" : tactic => `(tactic| (skip;sorry))
-- macro "later" : tactic => `(tactic| (sorry; fail "Proof deferred with 'later'"))

-- theorem epsilon_not_in_R : epsilon ∉ R_subset := by
lemma proper_extension : epsilon ∉ R_subset := by
  intro h
  obtain ⟨r0, hr⟩ := h  -- Assume ε = hyper r for some r ∈ ℝ
  later
  -- rfl
  -- skip
  -- admit
  -- sorry
  -- have k : epsilon < hyper r0 := epsilon_infinitesimal r0
  -- rw [hr] at k
  -- exact lt_irrefl _ k -- Contradiction ¬a < a


-- ⪦ ⫉ ⪽ ⪿ ⫁ ⫇
notation a " ⪽ " b => Nonempty (a ↪ b) -- Embedding (too weak, we have equivalence of subtypes)
theorem R_embedded0 : ℝ ⪽ ℝ* := -- as TYPES!
  ⟨R_subset_equivalent.toEmbedding.trans (Function.Embedding.subtype _)⟩

-- def R_subtype : Type := { x : R* // ∃ r : ℝ, x = hyper r }
-- instance : Coe R_subtype ℝ* := ⟨Subtype.val⟩ -- coercion from R to R*  ( R ≃ ℝ )

-- notation a " ⪦ " b  " a is equivalent/homomorphic to a subtype of b"
-- notation a " ⪦ " b => Nonempty (a ≃ { x : b // P x })
-- notation a " ⪦ " b => ∃ c, (a ≃ c) ∧ (c ↪ b) -- Subtype Embedding
-- notation a " ⪦ " b => ∃ (c : Type b), Nonempty ( a ≃ c )
-- notation a " ⪦ " b => Nonempty (Σ (c : Type b), (a ≃ c) × (a ↪ b))
notation a " ⪦ " b => Nonempty (Σ (c : Type), (a ≃ c) × (c ↪ b))

theorem R_as_subtype : ℝ ⪦ ℝ* :=
  ⟨⟨R_subtype, R_subtype_equiv, ⟨Subtype.val, Subtype.coe_injective⟩⟩⟩

theorem R_is_subset : R_subset ⊆ Hyperreals := by
  simp [R_subset, Hyperreals]

-- notation a " ⫇ " b => Set a ⊆ Set b -- Subset Embedding via intermediate equivalence embedding
notation a " ⫇ " b => ∃ (c : Set b), Nonempty ( a ≃ c )

theorem R_as_subset : ℝ ⫇ R* := by
  let c := R_subset
  have h1 : Nonempty (ℝ ≃ c) := ⟨R_subset_equivalent⟩
  exact ⟨c, h1⟩

def simplify (x : R*) : R* := x -- identity function HERE, for compatibility with HyperList proofs …

theorem unique_real_infinite_close (x : R*) : finite x → ∃! r : ℝ, x ≈ hyper r :=
  sorry

end HyperKeisler
end Hypers
