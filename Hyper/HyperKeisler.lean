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

axiom Hyperreal : Type
-- notation "Hyper" => Hyperreal
notation "R*" => Hyperreal
notation "ℝ*" => Hyperreal
notation "R+" => { r : ℝ // r > 0 }
notation "ℝ+" => { r : ℝ // r > 0 }

-- Hyperreal as a set! ⚠️ Hyperreal ≠ Hyperreals ⚠️ confusion!
-- def Hyperreals : Set R* := Set.univ  -- The set of all hyperreal numbers (trivial & redundant!)
--  redundant since R* already represents all hyperreal numbers as a type.

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
axiom extension : ℝ →+* R*

-- axiom extension : ℝ → R*   -- without RingHom which we would have to add later

-- noncomputable instance : Ring R* := inferInstance -- Ring follows from LinearOrderedField
-- Ring Homomorphism / Field Homomorphism
-- axiom extension_hom : RingHom ℝ R* extension
-- axiom extension_hom : FieldHom ℝ R* extension

-- TODO we MAY make this all computable by giving a definition like
-- structure HyperGeneral :=
--   components : List (𝔽 × 𝔽)

-- Coerce real numbers into hyperreal numbers
-- Automatically infer Coe from RingHom
noncomputable instance : Coe ℝ R* := ⟨extension⟩
noncomputable instance : Coe ℕ R* := ⟨λ n => extension (n : ℝ)⟩
noncomputable instance : Coe ℤ R* := ⟨λ z => extension (z : ℝ)⟩
noncomputable instance : Coe ℚ R* := ⟨λ q => extension (q : ℝ)⟩
-- noncomputable instance : Coe ℝ R* := ⟨extension.toFun⟩

-- Order compatibility with ℝ
axiom ordered_field_extension : ∀ (r s : ℝ), extension r < extension s ↔ r < s

-- theorem ordered_field_transfer (r : ℝ) (s : ℝ*) : r < s ↔ extension r < s :=
--   ordered_field_extension r (coe s)

-- heterogeneous order relation or coercive order
-- apply '<' to ℝ and ℝ*  e.g. 0 < extension 1 !
axiom ordered_field_transfer : ∀ (r : ℝ) , (s : ℝ*) → (r < s ↔ extension r < s)
axiom ordered_field_reverse : ∀ (s : ℝ*) (r : ℝ), s < r ↔ s < extension r
-- TODO: proof that these follow IF THEY DO:
-- axiom ordered_field_transfer_z : ∀ (r : ℝ) (s : ℝ*), (∃ z : ℝ*, z = extension r) → (r < s ↔ z < s)
-- axiom ordered_field_transfer_z2 : ∀ (r : ℝ) (s : ℝ*) (z : ℝ*), z = extension r → (r < s ↔ z < s)

-- axiom ordered_field_transfer_RR2 : ∀ (r s : ℝ) , r < s ↔ r < extension s
theorem ordered_field_transfer_RR2 (r s : ℝ) : r < s ↔ r < extension s :=
  (ordered_field_extension r s).symm.trans
    (ordered_field_transfer r (extension s)).symm
#print axioms ordered_field_transfer_RR2

/--
From the coercion `Coe ℝ R* := ⟨extension⟩`, `r < s` for `s : ℝ` implicitly means
`r < (s : R*) = extension s`. Hence if `z = extension s`, the two inequalities
`r < s` and `r < z` coincide definitionally.
-/
theorem ordered_field_transfer2 (r : R*) (s : ℝ) (z : R*) (hz : z = extension s) : r < s ↔ r < z :=
  by rw [← hz]  -- both sides mean `r < extension s`


-- Axiom C: Existence of a positive infinitesimal ε
axiom epsilon : R*
axiom infinitesimal_pos : 0 < epsilon ∧ ∀ r : ℝ, epsilon < extension r

-- Extend the order: ℝ is naturally embedded in Hyperreal
axiom real_le_hyperreal : ∀ r : ℝ, ∀ x : R*, (r : R*) ≤ x ↔ (extension r) ≤ x

-- Axiom D: Natural extension of functions

-- Notation for R*ⁿ *Rⁿ Hyperreal vectors
notation "R*"n => (Fin n → R*) -- STILL needs to be wrapped as (R*n) WHY?
-- notation "R^"n => (Fin n → ℝ) ambiguous :
notation "ℝ^"n => (Fin n → ℝ)
-- notation "ℝⁿ" => Fin n → ℝ

axiom D : ∀ {n : ℕ} (f : (ℝ^n) → ℝ),
  ∃ f_star : (R*n) → R*,
  ∀ (x : ℝ^n), f_star (extension ∘ x) = extension (f x)

-- Axiom E: Transfer principle
axiom E : ∀ (P : R* → Prop), (∀ r : ℝ, P (extension r)) → (∀ x : R*, P x)

-- Axiom F: Standard part function
axiom st : R* → ℝ
notation "real" => st -- alias real part of a hyperreal akin to `Re` in complex numbers
notation "standard" => st --  noncomputable def standard := st -- alias
axiom st_extension : ∀ r : ℝ, st (extension r) = r
axiom extension_st : ∀ r : ℝ, extension (st r) = r -- todo: as lemma

lemma st_extension' (r : ℝ) : st (r : R*) = r := st_extension r -- via coercion
#eval epsilon.real -- 0.0
-- Definition 1.1: Infinitesimals, finites, and infinite elements
def finite  (x : R*) : Prop := ∃ r : ℝ, |x| < extension r
def infinite  (x : R*) : Prop := ∀ r : ℝ, r > 0 → |x| > extension r
def infinitesimal (x : R*) : Prop := ∀ r : ℝ, r > 0 → |x| < extension r
-- def infinitesimal2 (x : R*) : Prop := ∀ r : R+, |x| < extension r
-- lemma infinitesimal_iff_infinitesimal2 : infinitesimal x ↔ infinitesimal2 x :=
--   by simp [infinitesimal, infinitesimal2]

def near (x y : R*) : Prop := infinitesimal (x - y)
def cofinite (x y : R*) : Prop := finite (x - y)
-- def near (x y : R*) : Prop := infinitesimal extension (x - y)

-- Definition 1.2: Monad and Galaxy
def monad (x : R*) : Set R* := {y | near x y}
def galaxy (x : R*) : Set R* := {y | finite (x - y)}
-- def galaxy' (x : R*) : Set R* := {y | finite (y - x)}
-- def galaxy (x : R*) : Set R* := {y | cofinite (x y)}
def halo := monad -- alias

-- def Finites : Set R* := galaxy 0
def Finites : Set R* := {y | finite y} --  galaxy 0
def Infinitesimals : Set R* := {y | infinitesimal y} -- monad 0
def Infinites : Set R* := {y | infinite y} --
-- def Infinites : Set R* := {y | ¬ finite y}  -- Equivalent to the complement of galaxy(0)
-- def Infinites : Set R* := R* \ Finites  -- Complement of the finite set R* error, R* is a Type!
-- def Infinites : Set R* := Set.univ \ Finites  -- Complement of the finite set R*
-- Set R* represents the type of all subsets of  R^ *.
-- •	Set.univ is the universal set in Lean, meaning the set of all elements of  R^ *.


lemma extension_zero : extension 0 = (0 : R*) :=
  by exact extension.map_zero

lemma zero_is_infinitesimal : infinitesimal (0 : R*) := by
  intro r hr
  -- By definition, "infinitesimal (0 : R*)" means ∀ r>0, |0| < extension r
  simp only [infinitesimal, abs_zero]
  -- Show 0 < extension r
  rw [← extension_zero]      -- replace 0 with extension 0
  exact (ordered_field_extension 0 r).mpr hr


-- Notation for near (≈)
-- notation x " ≈ " y => (near x y)
-- #print notation =  => 50, use that same precedence
infix:50 " ≈ " => near
infix:50 " ∻ " => cofinite -- ∺ within same galaxy 🌌

-- (a,∞) = {x: a<x}
notation "(" a ",∞)" => Set.Ioi a

-- (-∞,a) = {x: x<a}
notation "(-∞," a ")" => Set.Iio a

-- (-∞,∞) = R
notation "(-∞,∞)" => Set.Univ


-- Coercion from R to R* works
example (r : ℝ) (x : R*) : r + x = extension r + x := rfl
example (r : ℝ) : r = extension r := rfl

def R_subset : Set R* := Set.range extension
def R_subtype : Type := { x : R* // ∃ r : ℝ, x = extension r }

lemma st_is_inverse (x : R*) (h : x ∈ R_subset) : extension (st x) = x := by
  obtain ⟨r, hr⟩ := h -- x = extension r for some r ∈ ℝ
  have h0 : extension r = x := hr
  have h1 : st x = r := by rw [←h0, st_extension]
  rw [h1]
  exact hr

noncomputable def st_R_subset : R_subset → ℝ := λ x => st x -- standard part of x in R_subset

@[simps apply]
noncomputable def R_embedded_equivalent : ℝ ≃ R_subset := {
  toFun := λ r => ⟨extension r, ⟨r, rfl⟩⟩,
  invFun := st_R_subset,
  left_inv := λ r => by simp [st_R_subset, st_extension],
  right_inv := λ ⟨x, ⟨r, hr⟩⟩ => by
    show (⟨extension (st x), ⟨st x, rfl⟩⟩ : R_subset) = ⟨x, ⟨r, hr⟩⟩
    apply Subtype.ext
    show extension (st x) = x
    rw [← hr, extension_st]
}

-- TODO: Define R as a subtype of R*
-- axiom R_star_superset : ℝ ⊂ R* for types :(
-- axiom R_real_subtype : ℝ = R_subtype -- CHAOS! don't do this!
-- noncomputable def R_subtype_equiv : ℝ ≃ R_subtype := {
--   toFun := λ r => ⟨extension r, ⟨r, rfl⟩⟩,
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
  obtain ⟨r, hr⟩ := h  -- Assume ε = extension r for some r ∈ ℝ
  have h1 : 0 < epsilon := infinitesimal_pos.1
  have h2 : epsilon < extension (r + 1) := infinitesimal_pos.2 (r + 1)
  have h3 : extension r < extension (r + 1) := by rw [hr]
  rw [hr] at h1 h2
  show False
  contradiction
  -- linarith
  -- by_contradiction


noncomputable def real_homeo : ℝ ≃ₜ R :=
{ toFun := extension,
  invFun := st, -- assuming `st` is well-defined
  left_inv := st_extension, -- st(extension r) = r
  right_inv := λ x, by
    { rcases x with ⟨r, hr⟩,
      exact Subtype.ext (st_extension r) },
  continuous_toFun := sorry, -- Follows from standard topology properties
  continuous_invFun := sorry } -- Needs proof from `st`


-- theorem R_star_superset : R_subset ⊂ Set.univ := by
-- theorem R_star_superset2 : R_subset ⊂ Hyperreals := by
--   rw [Set.ssubset_def]
--   constructor
--   · exact Set.subset_univ R_subset -- ℝ is a subset of ℝ*
--   · use epsilon -- Find an element in ℝ* that is not in ℝ
--     intro h
--     obtain ⟨r, hr⟩ := h -- Assume ε = extension r for some r ∈ ℝ
--     have h1 : 0 < epsilon := infinitesimal_pos.1
--     have h2 : epsilon < extension (r + 1) := infinitesimal_pos.2 (r + 1)
--     rw [hr] at h1 h2 -- Substitute ε = extension r
--     linarith -- Contradiction

-- notation a "⫇" b  => R_subset ⊂ Set.univ


-- ⪦ ⫉ ⪽ ⪿ ⫁ ⫇
notation a " ⪽ " b => Nonempty (a ↪ b) -- Embedding (too weak, we have equivalence of subtypes)
theorem R_embedded0 : ℝ ⪽ ℝ* := -- as TYPES!
  ⟨R_embedded_equivalent.toEmbedding.trans (Function.Embedding.subtype _)⟩

-- notation a " ⪦ " b => Nonempty (a ≃ { x : b // P x })
notation a " ⪦ " b => ∃ c, (a ≃ c) ∧ (c ↪ b) -- Subtype Embedding
notation a " ⪦ " b => Nonempty (Σ c, (a ≃ c) × (c ↪ b))
theorem R_embedded : ℝ ⪦ ℝ* :=
  ⟨R_subtype, R_embedded_equivalent, Function.Embedding.subtype⟩

notation a " ⫇ " b => ∃ c, a ≃ c ∧ c ⊆ b -- Subset Embedding
theorem R_as_subset : Set.univ ℝ ⫇ Set.univ R* := by
  exact ⟨R_embedded_equivalent, R_subset⟩
