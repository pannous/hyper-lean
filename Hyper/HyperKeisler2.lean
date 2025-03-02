-- import Mathlib.Algebra.Order.Field
import Mathlib.Topology.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
-- notation "ℝ" => Real
-- notation "ℝ" => Float
notation "R" => ℝ

-- import Mathlib.Algebra.Order.Field
-- set_option checkBinderAnnotations false


set_option diagnostics true
set_option diagnostics.threshold 1000

-- class Hyperreal extends LinearOrderedField Hyperreal where
--   extension : ℝ → Hyperreal
--   ordered_field_extension : ∀ (r s : ℝ), extension r < extension s ↔ r < s
--   epsilon : Hyperreal
--   infinitesimal_pos : 0 < epsilon ∧ ∀ r : ℝ, epsilon < extension r

-- axiom Hyperreal : Type
-- axiom extension : ℝ → Hyperreal


-- -- Declare that Hyperreal is a LinearOrderedField, but defer the proof
-- axiom LinearOrderedField_Hyperreal : LinearOrderedField Hyperreal

-- -- Declare that Hyperreal is a linear ordered field
-- -- instance : LinearOrderedField Hyperreal := LinearOrderedField_Hyperreal
-- noncomputable instance : LinearOrderedField Hyperreal := LinearOrderedField_Hyperreal

-- -- Axiom: Hyperreal extends ℝ as an ordered field
-- axiom ordered_field_extension : ∀ (r s : ℝ), extension r < extension s ↔ r < s

-- -- Axiom: Existence of an infinitesimal
-- axiom epsilon : Hyperreal
-- axiom infinitesimal_pos : 0 < epsilon ∧ ∀ r : ℝ, epsilon < extension r


-- structure Hyperreal where
--   Hyper : Type
--   [field_Hyper : LinearOrderedField Hyper] -- proof that Hyper has the structure of a linear ordered field
--   extension : ℝ → Hyper
--   epsilon : Hyper
--   infinitesimal_pos : 0 < epsilon ∧ ∀ r : ℝ, epsilon < extension r

structure Hyperreal (H : Type) [LinearOrderedField H] where
  extension : ℝ → H
  epsilon : H
  infinitesimal_pos : 0 < epsilon ∧ ∀ r : ℝ, epsilon < extension r

-- Now we can define an instance for any `H` that satisfies this structure
instance (H : Type) [LinearOrderedField H] : CoeSort (Hyperreal H) Type := ⟨fun _ => H⟩
-- structure Hyperreal where
--   carrier : Type
--   [field_Hyper : LinearOrderedField carrier]
--   extension : ℝ → carrier
--   epsilon : carrier
--   infinitesimal_pos : 0 < epsilon ∧ ∀ r : ℝ, epsilon < extension r

-- -- Make Hyperreal behave like a type itself
-- instance : CoeSort Hyperreal Type := ⟨Hyperreal.carrier⟩

-- instance : LinearOrderedField Hyperreal.carrier := Hyperreal.field_Hyper

namespace Hyperreal


axiom B : ∀ (r s : ℝ), H.extension r < H.extension s ↔ r < s
axiom B : ∀ (r s : ℝ), Hyperreal.extension r < Hyperreal.extension s ↔ r < s
-- Axiom B: R* is an ordered field extension of R
-- axiom B : ∀ (r s : R), H.extension r < H.extension s ↔ r < s
-- axiom B : ∀ (r s : ℝ), H.extension r < H.extension s ↔ r < s
-- axiom B : ∀ (r s : ℝ), @LT.lt H.Hyper _ (H.extension r) (H.extension s) ↔ r < s
-- axiom B : ∀ (r s : ℝ), @LT.lt H.Hyper H.field_Hyper.toLT (H.extension r) (H.extension s) ↔ r < s

-- Axiom C: Existence of a positive infinitesimal ε
-- axiom C : H.infinitesimal_pos -- already defined in the structure


-- Axiom D: Natural extension of functions
axiom D : ∀ {n : ℕ} (f : (Fin n → ℝ) → ℝ),
  ∃ f_star : (Fin n → H.Hyper) → H.Hyper,
  ∀ (x : Fin n → ℝ), f_star (H.extension ∘ x) = H.extension (f x)

-- axiom D2 : ∀ {n : ℕ} (f : ℝ^n → ℝ), ∃ f_star : H.Hyper^n → H.Hyper,
--   ∀ (x : ℝ^n), f_star (H.extension <$> x) = H.extension (f x)

-- axiom D2 : ∀ {n : ℕ} (f : R^n → R), ∃ f_star : H.Hyper^n → H.Hyper,
--   ∀ (x : R^n), f_star (H.extension <$> x) = H.extension (f x)

-- Axiom E: Transfer principle
axiom E : ∀ (P : H.Hyper → Prop), (∀ r : ℝ, P (H.extension r)) → (∀ x : H.Hyper, P x)

-- Definition 1.1: Infinitesimals, finites, and infinite elements
-- def is_infinitesimal (x : H.Hyper) : Prop := ∀ r : R, abs x < H.extension r
-- def is_finite (x : H.Hyper) : Prop := ∃ r : R, abs x < H.extension r
-- def is_infinite (x : H.Hyper) : Prop := ∀ r : R, abs x > H.extension r
def is_infinitesimal (H : Hyperreal) (x : H.Hyper) : Prop :=
  ∀ r : ℝ, |x| < H.extension r

def is_finite (H : Hyperreal) (x : H.Hyper) : Prop :=
  ∃ r : ℝ, |x| < H.extension r

def is_infinite (H : Hyperreal) (x : H.Hyper) : Prop :=
  ∀ r : ℝ, |x| > H.extension r


def infinitely_close (H : Hyperreal) (x y : H.Hyper) : Prop := is_infinitesimal (x - y)

-- Definition 1.2: Monad and Galaxy
def monad (x : H.Hyper) : Set H.Hyper := {y | infinitely_close x y}
def galaxy (x : H.Hyper) : Set H.Hyper := {y | is_finite (x - y)}

end Hyperreal
