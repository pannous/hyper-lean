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

-- set_option autoImplicit false -- to debug
-- set_option diagnostics true
-- set_option diagnostics.threshold 1000
-- set_option pp.all true
-- set_option checkBinderAnnotations false

-- ⚠️ Lean 4 DOES NOT CHECK SOUNDNESS OF AXIOMS ⚠️

-- [@implemented_by ] <<< only when executing code in Lean #eval, not in proofs
-- [@extern ...] fast C implementation
-- axiom Hyperreal : Type -- e.g.
-- structure Hyperreal' := (real : ℝ) (epsilon : ℝ)
structure Hyperreal' where
  real : ℝ
  hype : ℝ -- not to be confused with hyper(ℝ) embedding

-- 	•	Use a class only if you need multiple models of hyperreals.
--  ℝ (for proofs) and Float (for computation).
def Hyperreal := Hyperreal' -- Now they are the same

-- notation "Hyper" => Hyperreal
notation "R*" => Hyperreal
notation "ℝ*" => Hyperreal
notation "R+" => { r : ℝ // r > 0 }
notation "ℝ+" => { r : ℝ // r > 0 }

-- axiom R_subtype : ℝ ⊂ ℝ*

-- namespace Hyperreal
-- put at the end of the file:
-- end Hyperreal

-- In mathematics, the system of hyperreal numbers is a way of treating infinite and infinitesimal (infinitely small but non-zero) quantities. The hyperreals, or nonstandard reals, *R, are an extension of the real numbers R with elements ω ≈ ∞ and ε ≈ 1/∞ and their algebraic span.
-- 0 < ε < r ∀r∊ℝ⁺

-- Axiom A
-- R is a complete ordered field (yes just the real numbers, we know them)
notation "R" => ℝ

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

-- theorem ordered_field_transfer (r : ℝ) (s : ℝ*) : r < s ↔ hyper r < s :=
--   ordered_field_extension r (coe s)

-- heterogeneous order relation or coercive order
-- apply '<' to ℝ and ℝ*  e.g. 0 < hyper 1 !
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

axiom infinitesimal_pos : 0 < epsilon ∧ ∀ r : ℝ, epsilon < hyper r

-- Extend the order: ℝ is naturally embedded in Hyperreal
axiom real_le_hyperreal : ∀ r : ℝ, ∀ x : R*, (r : R*) ≤ x ↔ (hyper r) ≤ x

-- Axiom D: Natural extension of functions

-- Notation for R*ⁿ *Rⁿ Hyperreal vectors
notation "R*"n => (Fin n → R*) -- STILL needs to be wrapped as (R*n) WHY?
-- notation "R^"n => (Fin n → ℝ) ambiguous :
notation "ℝ^"n => (Fin n → ℝ)
-- notation "ℝⁿ" => Fin n → ℝ

axiom D : ∀ {n : ℕ} (f : (ℝ^n) → ℝ),
  ∃ f_star : (R*n) → R*,
  ∀ (x : ℝ^n), f_star (hyper ∘ x) = hyper (f x)

-- Axiom E: Transfer principle
axiom E : ∀ (P : R* → Prop), (∀ r : ℝ, P (hyper r)) → (∀ x : R*, P x)

-- Axiom F: Standard part function
-- axiom real : R* → ℝ -- noncomputable and we can't make it computable later
-- axiom real_part : R* → ℝ standard part
-- axiom hyper_part : R* → R* vs standard part
-- def real (x : R*) : ℝ := sorry -- Will be implemented later, e.g. :
-- def real (x : R*) : ℝ := x.real -- If implemented as a structure
def real : R* → ℝ
-- | epsilon => 0 -- "redundant"
| x       => x.real

-- structure Hyperreal' := (real : ℝ) (epsilon : ℝ)

class StandardPart (α : Type*) := (real : α → ℝ)

notation "st" => real -- alias st standard = real part of a hyperreal akin to `Re` in complex numbers
notation "standard" => real --  noncomputable def standard := real -- alias
axiom st_extension : ∀ r : ℝ, real (hyper r) = r
axiom extension_st : ∀ r : ℝ, hyper (real r) = r -- todo: as lemma
axiom pure_epsilon : real epsilon = 0  -- redundant but can't hurt
lemma pure_epsilon': real epsilon = 0  := by exact pure_epsilon -- simp [real] or pure_epsilon
#reduce real epsilon -- 0.0
-- noncomputable MTFK!!
-- #eval real epsilon -- 0.0

-- Add a "real" method to Hyperreal for accessing the standard part
-- @[inline] def Hyperreal.real (x : R*) : ℝ := real x -- already defined
-- #eval epsilon.real -- 0.0

lemma st_extension' (r : ℝ) : real (r : R*) = r := st_extension r -- via coercion
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
def R_subset : Set R* := {y | finite y ∧ ¬ infinitesimal y} -- ℝ embedded in R*
def R_subset' : Set R* := Set.range hyper -- ℝ embedded in R*
def Infinites' : Set R* := {y | ¬ finite y}  -- Equivalent to the complement of galaxy(0)
def Infinites'' : Set R* :=  Hyperreals \ Finites  -- Complement of the finite set
-- def Infinites : Set R* := Set.univ \ Finites  -- Complement of the finite set R*
-- Set R* represents the type of all subsets of  R^ *.
-- •	Set.univ is the universal set in Lean, meaning the set of all elements of  R^ *.

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
infix:50 " ≈ " => near
infix:50 " ∻ " => cofinite -- ∺ within same galaxy 🌌


-- Coercion from R to R* works
example (r : ℝ) (x : R*) : r + x = hyper r + x := rfl
example (r : ℝ) : r = hyper r := rfl

def R_subset : Set R* := Set.range hyper
def R_subtype : Type := { x : R* // ∃ r : ℝ, x = hyper r }

lemma st_is_inverse (x : R*) (h : x ∈ R_subset) : hyper (real x) = x := by
  obtain ⟨r, hr⟩ := h -- x = hyper r for some r ∈ ℝ
  have h0 : hyper r = x := hr
  have h1 : real x = r := by rw [←h0, st_extension]
  rw [h1]
  exact hr

noncomputable def st_R_subset : R_subset → ℝ := λ x => real x -- standard part of x in R_subset

@[simps apply] -- ≃ Equiv Equivalence
noncomputable def R_embedded_equivalent : ℝ ≃ R_subset := {
  toFun := λ r => ⟨hyper r, ⟨r, rfl⟩⟩, -- 𝞅
  invFun := st_R_subset, -- 𝞅⁻¹
  left_inv := λ r => by simp [st_R_subset, st_extension], -- 𝞅⁻¹•𝞅=1
  right_inv := λ ⟨x, ⟨r, hr⟩⟩ => by -- 𝞅•𝞅⁻¹=1
    show (⟨hyper (real x), ⟨real x, rfl⟩⟩ : R_subset) = ⟨x, ⟨r, hr⟩⟩
    apply Subtype.ext
    show hyper (real x) = x
    rw [← hr, extension_st]
}

-- TODO: Define R as a subtype of R*
-- axiom R_star_superset : ℝ ⊂ R* for types :(
-- axiom R_real_subtype : ℝ = R_subtype -- CHAOS! don't do this!
-- noncomputable def R_subtype_equiv : ℝ ≃ R_subtype := {
--   toFun := λ r => ⟨hyper r, ⟨r, rfl⟩⟩,
--   invFun := sorry, --λ ⟨x, ⟨r, hr⟩⟩ => r,
--   left_inv := λ r => rfl,
--   right_inv := λ ⟨x, ⟨r, hr⟩⟩ => by
--     apply Subtype.ext
--     exact hr
-- }


instance : Coe R+ ℝ := ⟨Subtype.val⟩ -- coercion from R+ to ℝ


-- theorem epsilon_not_in_R : epsilon ∉ R_subset := by
lemma proper_extension : epsilon ∉ R_subset := by
  intro h
  obtain ⟨r, hr⟩ := h  -- Assume ε = hyper r for some r ∈ ℝ
  have h1 : 0 < epsilon := infinitesimal_pos.1
  have h2 : epsilon < hyper (r + 1) := infinitesimal_pos.2 (r + 1)
  have h3 : hyper r < hyper (r + 1) := by rw [hr]
  rw [hr] at h1 h2
  show False
  contradiction
  -- linarith
  -- by_contradiction

notation a "≃ₜ" b => Nonempty (a ≃ b) -- Topological Equivalence

noncomputable def real_homeo : ℝ ≃ₜ R :=
{ toFun := hyper,
  invFun := real, -- assuming `real` is well-defined
  left_inv := st_extension, -- real(hyper r) = r
  right_inv := λ x, by
    { rcases x with ⟨r, hr⟩,
      exact Subtype.ext (st_extension r) },
  continuous_toFun := sorry, -- Follows from standard topology properties
  continuous_invFun := sorry } -- Needs proof from `real`


-- theorem R_star_superset : R_subset ⊂ Set.univ := by
-- theorem R_star_superset2 : R_subset ⊂ Hyperreals := by
--   rw [Set.ssubset_def]
--   constructor
--   · exact Set.subset_univ R_subset -- ℝ is a subset of ℝ*
--   · use epsilon -- Find an element in ℝ* that is not in ℝ
--     intro h
--     obtain ⟨r, hr⟩ := h -- Assume ε = hyper r for some r ∈ ℝ
--     have h1 : 0 < epsilon := infinitesimal_pos.1
--     have h2 : epsilon < hyper (r + 1) := infinitesimal_pos.2 (r + 1)
--     rw [hr] at h1 h2 -- Substitute ε = hyper r
--     linarith -- Contradiction

-- notation a "⫇" b  => R_subset ⊂ Set.univ


-- ⪦ ⫉ ⪽ ⪿ ⫁ ⫇
notation a " ⪽ " b => Nonempty (a ↪ b) -- Embedding (too weak, we have equivalence of subtypes)
theorem R_embedded0 : ℝ ⪽ ℝ* := -- as TYPES!
  ⟨R_embedded_equivalent.toEmbedding.trans (Function.Embedding.subtype _)⟩

-- notation a " ⪦ " b  " a is equivalent/homomorphic to a subtype of b"
-- notation a " ⪦ " b => Nonempty (a ≃ { x : b // P x })
-- notation a " ⪦ " b => ∃ c, (a ≃ c) ∧ (c ↪ b) -- Subtype Embedding
notation a " ⪦ " b => Nonempty (Σ c, (a ≃ c) × (c ↪ b))
theorem R_embedded : ℝ ⪦ ℝ* :=
  ⟨R_subtype, R_embedded_equivalent, Function.Embedding.subtype⟩

notation a " ⫇ " b => ∃ c, a ≃ c ∧ c ⊆ b -- Subset Embedding
-- theorem R_as_subset :  ℝ ⫇ R* := by
--   exact ⟨R_embedded_equivalent, R_subset⟩
theorem R_as_subset : Reals ⫇ Hyperreals := by
  exact ⟨R_embedded_equivalent, R_subset⟩

theorem R_as_subset : Set.univ ℝ ⫇ Set.univ R* := by
  exact ⟨R_embedded_equivalent, R_subset⟩
