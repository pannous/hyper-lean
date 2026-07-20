import Mathlib.Data.Real.Basic

-- Since everything here is defined axiomatically
-- everything needs to be marked as noncomputable but don't worry once it's compiled it will be computed anyways!!

notation "𝔽" => ℚ -- OUR FIELD!!
-- notation "𝔽" => ℝ -- OUR FIELD!!

axiom Hyperreal : Type -- e.g.:
-- def Hyperreal : Type := List (𝔽 × 𝔽)
notation "R*" => Hyperreal

axiom LinearOrderedField_Hyperreal : LinearOrderedField R* -- property
noncomputable instance : LinearOrderedField R* := LinearOrderedField_Hyperreal -- proof

axiom hyper : 𝔽 →+* R* -- embedding constructor is Ring homomorphism

notation "𝔽*" => Hyperreal
notation "ℝ*" => Hyperreal
notation "R+" => { r : ℝ // r > 0 }
notation "ℝ+" => { r : ℝ // r > 0 }


noncomputable instance : Coe 𝔽 𝔽* := ⟨hyper⟩
noncomputable instance : Coe ℕ R* := ⟨λ n => hyper (n : 𝔽)⟩
noncomputable instance : Coe ℤ R* := ⟨λ z => hyper (z : 𝔽)⟩
noncomputable instance : Coe ℚ R* := ⟨λ q => hyper (q : 𝔽)⟩
-- noncomputable instance : Coe ℝ R* := ⟨λ r => hyper (r : 𝔽)⟩ -- ℝ -> ℚ  not possible :(

-- Axiom C: Existence of a positive infinitesimal ε
axiom epsilon : R*
notation "ε" => epsilon
notation "ω" => epsilon⁻¹

axiom epsilon_pos : 0 < epsilon

-- Axiom C extension: ε is infinitesimal
axiom infinitesimal_pos : ∀ r : 𝔽, epsilon < hyper r

-- Order compatibility with 𝔽
axiom ordered_field_extension : ∀ (r s : 𝔽), hyper r < hyper s ↔ r < s

-- heterogeneous order relation or coercive order -- apply '<' to 𝔽 and 𝔽*  e.g. 0 < hyper 1 !
axiom ordered_field_transfer : ∀ (r : 𝔽) (s : 𝔽*), r < s ↔ hyper r < s
axiom ordered_field_reverse : ∀ (s : 𝔽*) (r : 𝔽), s < r ↔ s < hyper r


-- Extend the order: ℝ is naturally embedded in Hyperreal
axiom real_le_hyperreal : ∀ r : 𝔽 , ∀ x : R*, (r : R*) ≤ x ↔ (hyper r) ≤ x

-- Notation for R*ⁿ *Rⁿ Hyperreal vectors
notation "R*"n => (Fin n → R*) -- STILL needs to be wrapped as (R*n) WHY?
notation "𝔽^"n => (Fin n → 𝔽)
-- notation "ℝ^"n => (Fin n → ℝ)
-- notation "*ℝⁿ" => Fin n → ℝ*

-- Axiom D: Natural extension of functions
axiom D : ∀ {n : ℕ} (f : R* → 𝔽),
  ∃ f_star : (R*n) → R*,
  ∀ (x : 𝔽^n), f_star (hyper ∘ x) = hyper (f x)


-- Axiom E: Transfer principle
axiom E : ∀ (P : R* → Prop), (∀ r : 𝔽, P (hyper r)) → (∀ x : R*, P x)


-- Axiom F: Standard part function
axiom st : R* → 𝔽 -- noncomputable and we can't make it computable later

axiom st_extension : ∀ r : 𝔽 , st (hyper r) = r
axiom extension_st : ∀ r : 𝔽 , hyper (st r) = r -- todo: as lemma
axiom pure_epsilon : st epsilon = 0  -- redundant but can't hurt

def finite  (x : R*) : Prop := ∃ r : 𝔽 , |x| < hyper r
-- def infinite  (x : R*) : Prop := ∀ r : 𝔽, r > 0 → |x| > hyper r
-- def infinitesimal (x : R*) : Prop := ∀ r : 𝔽, r > 0 → |x| < hyper r
-- def infinitesimal0 (x : R*) : Prop := ∃ r : 𝔽 , x = r*ε -- excluding ε^2 !
-- def infinite0 (x : R*) : Prop := ∃ r : 𝔽 , x = r*ω -- excluding ω^2 + xyz !
def infinite (x : R*) : Prop := ∃ r : 𝔽 , |x| > r*ω
def infinitesimal (x : R*) : Prop := ∃ r : 𝔽 , |x| < r*ε -- including ε^2 !
def hyperinteger (x : R*) : Prop := ∃ r : Nat , x = r*ω


def near (x y : R*) : Prop := infinitesimal (x - y)
def cofinite (x y : R*) : Prop := finite (x - y)
-- def near (x y : R*) : Prop := infinitesimal hyper (x - y)

-- Definition 1.2: Monad and Galaxy
def monad (x : R*) : Set R* := {y | near x y}
def galaxy (x : R*) : Set R* := {y | finite (x - y)}
-- def galaxy' (x : R*) : Set R* := {y | finite (y - x)}
-- def galaxy (x : R*) : Set R* := {y | cofinite (x y)}
def halo := monad -- alias
