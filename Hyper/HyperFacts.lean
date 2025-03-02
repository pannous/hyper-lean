import Mathlib.Topology.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Linarith
import Hyper.HyperKeisler
-- import Mathlib.Logic.Classical

namespace Hyperreal
-- axiom Hyperreal : Type

-- variable {Hyperreal : Type} [LinearOrderedField Hyperreal] (extension : ℝ →+* Hyperreal)
--   (ordered_field_extension : ∀ (r s : ℝ), extension r < extension s ↔ r < s)
--   (epsilon : Hyperreal)
--   (infinitesimal_pos : 0 < epsilon ∧ ∀ r : ℝ, epsilon < extension r)

-- using  triangle inequality
-- abs_add (a b : α) : |a + b| ≤ |a| + |b|

-- Instead of defining new axioms we can infer it from our given axioms:
-- axiom near_refl : ∀ x : R*, near x x
-- axiom near_symm : ∀ x y : R*, near x y → near y x
-- axiom near_trans : ∀ x y z : R*, near x y → near y z → near x z


lemma extension_zero : extension 0 = (0 : R*) :=
  by exact extension.map_zero

lemma zero_is_infinitesimal : infinitesimal (0 : R*) := by
  intro r hr
  -- By definition, "infinitesimal (0 : R*)" means ∀ r>0, |0| < extension r
  simp only [infinitesimal, abs_zero]
  -- Show 0 < extension r
  rw [← extension_zero]      -- replace 0 with extension 0
  exact (ordered_field_extension 0 r).mpr hr

lemma near_refl (x : R*) : x ≈ x := by
  show infinitesimal (x - x)
  rw [sub_self x]    -- rewrite (x - x) as 0
  exact zero_is_infinitesimal

lemma near_symm {x y : R*} : x ≈ y → y ≈ x := by
  -- near x y means infinitesimal (x - y).
  -- We must show infinitesimal (y - x).
  intro h
  intro r hr
  -- h says ∀ r>0, |x - y| < extension r.
  -- But |y - x| = |x - y|.
  specialize h r hr
  rwa [abs_sub_comm] at h


lemma near_trans {x y z : R*} (hxy : x ≈ y) (hyz : y ≈ z) : x ≈ z := by
  unfold near at hxy hyz
  intro r hr
  calc
    |x - z|
      = |(x - y) + (y - z)| := by
        -- This lemma states x - z = (x - y) + (y - z)
        rw [← sub_add_sub_cancel x y z]
    _ ≤ |x - y| + |y - z| := abs_add _ _
    _ < extension (r / 2) + extension (r / 2) := by
      have hr2 : r / 2 > 0 := by linarith
      exact add_lt_add (hxy (r/2) hr2) (hyz (r/2) hr2)
    _ = extension ((r / 2) + (r / 2)) := by rw [extension.map_add]
    _ = extension r := by simp



instance near_is_equivalence : Equivalence near where
  refl  := near_refl
  symm  := near_symm
  trans := near_trans



-- Theorem 1.3. The set Finite = galaxy(0) of finite elements is a subring of R∗, that
-- is, sums, diﬀerences, and products of finite elements are finite.
theorem galaxy_zero_subring :
  ∀ x y : R*, finite x → finite y → finite (x + y) ∧ finite (x - y) ∧ finite (x * y) :=
by
  intro x y hx hy
  obtain ⟨r, hr⟩ := hx
  obtain ⟨s, hs⟩ := hy
  apply And.intro
  · use r + s
    rw [extension.map_add]  -- Uses RingHom property
    apply lt_of_le_of_lt (abs_add x y)
    exact add_lt_add hr hs
  · apply And.intro
    · use r + s
      rw [extension.map_add]
      apply lt_of_le_of_lt (abs_sub x y)
      exact add_lt_add hr hs
    · use r * s
      rw [extension.map_mul, abs_mul]  -- Uses RingHom property
      apply mul_lt_mul'' hr hs (abs_nonneg x) (abs_nonneg y)

-- Corollary 1.4. Any two galaxies are either equal or disjoint.
open Classical

lemma galaxy_intersection_near : ∀ x y z : R*, z ∈ galaxy x ∩ galaxy y → x ≈ y :=
by
  intro x y z hz
  rw [Set.mem_inter_iff] at hz  -- Unpack z ∈ galaxy x ∩ galaxy y
  have h1 : x ≈ z := hz.1  -- By definition of galaxy
  have h2 : near y z := hz.2  -- By definition of galaxy
  exact near_is_equiv.2.2 h1 h2 -- Apply transitivity of near


theorem galaxies_equal_or_disjoint : ∀ x y : R*, galaxy x = galaxy y ∨ galaxy x ∩ galaxy y = ∅ :=
by
  intro x y
  by_cases h : galaxy x = galaxy y
  · exact Or.inl h
  · apply Or.inr
    rw [Set.eq_empty_iff_forall_not_mem]
    intro z hz
    have h1 : near x z := by rw [Set.mem_setOf_eq] at hz; exact hz.1
    have h2 : near y z := by rw [Set.mem_setOf_eq] at hz; exact hz.2
    have h3 : near x y := near_equiv.trans h1 h2  -- Nearness is transitive
    have h4 : galaxy x = galaxy y := Set.ext (λ w, ⟨
      fun hw => near_equiv.trans h3 hw,
      fun hw => near_equiv.trans (near_equiv.symm h3) hw⟩)
    contradiction
theorem galaxies_equal_or_disjoint : ∀ x y : R*, galaxy x = galaxy y ∨ galaxy x ∩ galaxy y = ∅ :=
by
  intro x y
  by_cases h : galaxy x = galaxy y
  · exact Or.inl h
  · apply Or.inr
    rw [Set.eq_empty_iff_forall_not_mem]
    intro z hz
    have subset_contradiction : galaxy x ⊆ galaxy y → galaxy y ⊆ galaxy x → False :=
      fun h1 h2 => h (Set.Subset.antisymm h1 h2)
    exact subset_contradiction (Set.inter_subset_left _ _) (Set.inter_subset_right _ _) hz

theorem galaxies_equal_or_disjoint : ∀ x y : R*, galaxy x = galaxy y ∨ galaxy x ∩ galaxy y = ∅ :=
by
  intro x y
  by_cases h : galaxy x = galaxy y
  · exact Or.inl h
  · apply Or.inr
    rw [Set.eq_empty_iff_forall_not_mem]
    intro z hz
    have h1 : galaxy x ⊆ galaxy y → galaxy x = galaxy y :=
      fun h' => Set.Subset.antisymm h' (h.symm ▸ Set.subset_refl _)
    have h2 : galaxy y ⊆ galaxy x → galaxy x = galaxy y :=
      fun h' => Set.Subset.antisymm (h.symm ▸ Set.subset_refl _) h'
    exact h (h1 (Set.inter_subset_left _ _)) (h2 (Set.inter_subset_right _ _))

theorem galaxies_equal_or_disjoint : ∀ x y : R*, galaxy x = galaxy y ∨ galaxy x ∩ galaxy y = ∅ :=
by
  intro x y
  by_cases h : galaxy x = galaxy y
  · exact Or.inl h
  · apply Or.inr
    rw [Set.eq_empty_iff_forall_not_mem]
    intro z hz
    have h1 : galaxy x ⊆ galaxy y → galaxy x = galaxy y :=
      fun h' => Set.Subset.antisymm h' (Set.subset_of_eq h.symm)
    have h2 : galaxy y ⊆ galaxy x → galaxy x = galaxy y :=
      fun h' => Set.Subset.antisymm (Set.subset_of_eq h.symm) h'
    exact h (h1 (Set.inter_subset_left _ _)) (h2 (Set.inter_subset_right _ _))

theorem galaxies_equal_or_disjoint : ∀ x y : R*, galaxy x = galaxy y ∨ galaxy x ∩ galaxy y = ∅ :=
by
  intro x y
  by_cases h : galaxy x = galaxy y
  · exact Or.inl h
  · apply Or.inr
    rw [Set.eq_empty_iff_forall_not_mem]
    intro z hz
    have subset_contradiction : galaxy x ⊆ galaxy y → False :=
      fun h' => h (Set.Subset.antisymm h' (Set.inter_subset_left (galaxy x) (galaxy y)))
    exact subset_contradiction (Set.inter_subset_right (galaxy x) (galaxy y)) hz

theorem galaxies_equal_or_disjoint : ∀ x y : R*, galaxy x = galaxy y ∨ galaxy x ∩ galaxy y = ∅ :=
by
  intro x y
  by_cases h : galaxy x = galaxy y
  · exact Or.inl h
  · apply Or.inr
    rw [Set.eq_empty_iff_forall_not_mem]
    intro z hz
    have subset_contradiction : galaxy x ⊆ galaxy y → galaxy x = galaxy y := fun h' => h h'
    exact subset_contradiction (Set.inter_subset_right (galaxy x) (galaxy y)) hz

theorem galaxies_equal_or_disjoint : ∀ x y : R*, galaxy x = galaxy y ∨ galaxy x ∩ galaxy y = ∅ :=
by
  intro x y
  by_cases h : galaxy x = galaxy y
  · exact Or.inl h
  · apply Or.inr
    rw [Set.eq_empty_iff_forall_not_mem]
    intro z hz
    have subset_contradiction : galaxy x ⊆ galaxy y → galaxy x = galaxy y := λ h', h h',
    exact subset_contradiction (Set.inter_subset_right (galaxy x) (galaxy y)) hz
    -- exact h (Set.Subset.antisymm hz)


theorem galaxies_equal_or_disjoint : ∀ x y : R*, galaxy x = galaxy y ∨ galaxy x ∩ galaxy y = ∅ :=
by
  intro x y
  by_cases h : galaxy x = galaxy y
  · exact Or.inl h
  · apply Or.inr
    rw [Set.eq_empty_iff_forall_not_mem]
    intro z hz
    have subset_contradiction : galaxy x ⊆ galaxy y → galaxy x = galaxy y := λ h', h h',
    exact subset_contradiction (Set.inter_subset_right (galaxy x) (galaxy y)) hz

theorem galaxies_equal_or_disjoint : ∀ x y : R*, galaxy x = galaxy y ∨ galaxy x ∩ galaxy y = ∅ :=
by
  intro x y
  cases em (galaxy x = galaxy y) with h h
  · exact Or.inl h
  · exact Or.inr (Set.eq_empty_iff_forall_not_mem.mpr (λ z hz, h (Set.subset.antisymm hz)))





-- Theorem 1.4. The set Infinitesimal of inﬁnitesimal elements is an ideal of Finite.
theorem infinitesimal_ideal : ∀ x y : R*, finite x → infinitesimal y → finite (x * y) :=
by
  intro x y hx hy
  obtain ⟨r, hr⟩ := hx
  obtain ⟨s, hs⟩ := hy
  use r * s
  rw [extension.map_mul, abs_mul]  -- Uses RingHom property
  apply mul_lt_mul'' hr hs (abs_nonneg x) (abs_nonneg y)
