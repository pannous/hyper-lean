-- import Mathlib.Algebra.Order.Field
import Mathlib.Topology.Basic
import Mathlib.Algebra.Order.Field.Basic
-- import Mathlib.Algebra.Order.Field
-- set_option checkBinderAnnotations false


set_option diagnostics true
set_option diagnostics.threshold 1000

-- Define the structure of the hyperreal number system
structure Hyperreal (R : Type) [LinearOrderedField R] where
  Hyper : Type
  [field_Hyper : LinearOrderedField Hyper]
  extension : R → Hyper -- R*
  epsilon : Hyper
  infinitesimal_pos : 0 < epsilon ∧ ∀ r : R, epsilon < extension r

namespace Hyperreal

variable {R : Type} [LinearOrderedField R] (H : Hyperreal R)

-- Axiom A: R is a complete ordered field (assumed through Lean's LinearOrderedField)
axiom A : ∀ (r : R), true

-- Axiom B: R* is an ordered field extension of R
axiom B : ∀ (r s : R), H.extension r < H.extension s ↔ r < s
-- axiom B : ∀ (r s : R), @LT.lt H.Hyper _ (H.extension r) (H.extension s) ↔ r < s

-- Axiom C: Existence of a positive infinitesimal ε
axiom C : H.infinitesimal_pos

-- Axiom D: Natural extension of functions
axiom D : ∀ {n : ℕ} (f : R^n → R), ∃ f_star : H.Hyper^n → H.Hyper,
  ∀ (x : R^n), f_star (H.extension <$> x) = H.extension (f x)

-- Axiom E: Transfer principle
axiom E : ∀ (P : R → Prop), (∀ r : R, P r) → (∀ Hyper : H.Hyper, P (H.extension Hyper))

-- Definition 1.1: Infinitesimals, finites, and infinite elements
def is_infinitesimal (x : H.Hyper) : Prop := ∀ r : R, abs x < H.extension r
def is_finite (x : H.Hyper) : Prop := ∃ r : R, abs x < H.extension r
def is_infinite (x : H.Hyper) : Prop := ∀ r : R, abs x > H.extension r

def infinitely_close (x y : H.Hyper) : Prop := is_infinitesimal (x - y)

-- Definition 1.2: Monad and Galaxy
def monad (x : H.Hyper) : Set H.Hyper := {y | infinitely_close x y}
def galaxy (x : H.Hyper) : Set H.Hyper := {y | is_finite (x - y)}

end Hyperreal
