-- import Mathlib.Algebra.Order.Field
import Mathlib.Topology.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Ring.Hom.Defs
-- import Mathlib.Algebra.Field.Hom.Defs

set_option diagnostics true
set_option diagnostics.threshold 1000
-- set_option checkBinderAnnotations false

axiom Hyperreal : Type
-- notation "Hyper" => Hyperreal
notation "R*" => Hyperreal
notation "R+" => { r : ℝ // r > 0 }
notation "ℝ+" => { r : ℝ // r > 0 }
instance : Coe R+ ℝ := ⟨Subtype.val⟩ -- coercion from R+ to ℝ

-- namespace Hyperreal
-- put at the end of the file:
-- end Hyperreal

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

-- Coerce real numbers into hyperreal numbers
-- Automatically infer Coe from RingHom
noncomputable instance : Coe ℝ R* := ⟨extension⟩
-- noncomputable instance : Coe ℝ R* := ⟨extension.toFun⟩

-- Order compatibility with ℝ
axiom ordered_field_extension : ∀ (r s : ℝ), extension r < extension s ↔ r < s

-- Axiom C: Existence of a positive infinitesimal ε
axiom epsilon : R*
axiom infinitesimal_pos : 0 < epsilon ∧ ∀ r : ℝ, epsilon < extension r

-- Extend the order: ℝ is naturally embedded in Hyperreal
axiom real_le_hyperreal : ∀ r : ℝ, ∀ x : R*, (r : R*) ≤ x ↔ (extension r) ≤ x

-- Axiom D: Natural extension of functions
axiom D : ∀ {n : ℕ} (f : (Fin n → ℝ) → ℝ),
  ∃ f_star : (Fin n → R*) → R*,
  ∀ (x : Fin n → ℝ), f_star (extension ∘ x) = extension (f x)


-- Axiom E: Transfer principle
axiom E : ∀ (P : R* → Prop), (∀ r : ℝ, P (extension r)) → (∀ x : R*, P x)

-- Definition 1.1: Infinitesimals, finites, and infinite elements
def finite  (x : R*) : Prop := ∃ r : ℝ, |x| < extension r
def infinite  (x : R*) : Prop := ∀ r : ℝ, r > 0 → |x| > extension r
def infinitesimal (x : R*) : Prop := ∀ r : ℝ, r > 0 → |x| < extension r
-- def infinitesimal2 (x : R*) : Prop := ∀ r : R+, |x| < extension r
-- lemma infinitesimal_iff_infinitesimal2 : infinitesimal x ↔ infinitesimal2 x :=
--   by simp [infinitesimal, infinitesimal2]

def near (x y : R*) : Prop := infinitesimal (x - y)
-- def near (x y : R*) : Prop := infinitesimal extension (x - y)

-- Definition 1.2: Monad and Galaxy
def monad (x : R*) : Set R* := {y | near x y}
def galaxy (x : R*) : Set R* := {y | finite (x - y)}
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

-- Notation for near (≈)
-- notation x " ≈ " y => (near x y)
-- #print notation =  => 50, use that same precedence
infix:50 " ≈ " => near

-- Notation for R*^n (R*n)
notation "R*"n => Fin n → R*

-- (a,∞) = {x: a<x}
notation "(" a ",∞)" => Set.Ioi a

-- (-∞,a) = {x: x<a}
notation "(-∞," a ")" => Set.Iio a

-- (-∞,∞) = R
notation "(-∞,∞)" => Set.Univ
