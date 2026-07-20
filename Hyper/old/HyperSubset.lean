import Mathlib.Data.Real.Basic

axiom Hyperreal : Type

notation "R*" => Hyperreal
notation "ℝ*" => Hyperreal

axiom LinearOrderedField_Hyperreal : LinearOrderedField R* -- property

noncomputable
instance : LinearOrderedField R* := LinearOrderedField_Hyperreal -- proof

axiom hyper : ℝ →+* R* -- embedding constructor is Ring homomorphism

noncomputable instance : Coe ℝ ℝ* := ⟨hyper⟩
noncomputable instance : Coe ℕ R* := ⟨λ n => hyper (n : ℝ)⟩
noncomputable instance : Coe ℤ R* := ⟨λ z => hyper (z : ℝ)⟩
noncomputable instance : Coe ℚ R* := ⟨λ q => hyper (q : ℝ)⟩




-- Order compatibility with ℝ
axiom ordered_field_extension : ∀ (r s : ℝ), hyper r < hyper s ↔ r < s
-- heterogeneous order relation or coercive order -- apply '<' to ℝ and ℝ*  e.g. 0 < hyper 1 !
axiom ordered_field_transfer : ∀ (r : ℝ) (s : ℝ*), r < s ↔ hyper r < s
axiom ordered_field_reverse : ∀ (s : ℝ*) (r : ℝ), s < r ↔ s < hyper r

class IsProperSubtype (A B : Type) : Prop where
  coe : Coe A B
  proper : ∃ (S : Set B), (Set.range coe = S) ∧ S ⊂ Set.univ


class IsProperSubtype2 (A B : Type) : Prop where
  -- coe : Coe A B
  -- proper : ∃ (S : Set B), (Set.range (fun x : A => coe x) = S) ∧ S ⊂ Set.univ
  proper : ∃ (S : Set B), (Set.range (fun x : A => (x : B)) = S) ∧ S ⊂ Set.univ


class IsProperSubtype (A B : Type) : Prop where
  coe : Coe A B
  proper : ∃ (S : Set B), (Set.range (coe : A → B) = S) ∧ S ⊂ Set.univ

class IsProperSubtype (A B : Type) : Prop where
  as_set : Set B
  subset_axiom : (Set.univ : Set A) ⊆ as_set
  strict : (Set.univ : Set A) ≠ as_set

class IsSubtype (A B : Type) : Prop where
  coe : Coe A B
  nontrivial : Nonempty A → Nonempty B  -- Ensures A is nonempty only if B is.

notation A "⪽" B => IsSubtype A B

axiom R_subtype : ℝ ⪽ ℝ* -- theoretically but we don't want to inherit lean's structure of ℝ

def R_subset : Set R* := Set.range hyper


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


def dot : R* → R* := λ x => -- implementation of dot function here
  -- 1 iff x in halo of 0
  if x ∈ halo(x) then 1 else 0
