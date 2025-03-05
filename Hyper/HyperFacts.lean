import Mathlib.Topology.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Set.Basic -- nonempty => exists in set
import Mathlib.Algebra.Ring.Subring.Basic
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

def Finites : Set R* := {y | finite y} --  galaxy 0

-- function expected at
--   Subring ↑Finites
-- term has type
--   Type
instance finites_are_subring : Subring finite R* where
  zero_mem := by
    -- `0` is finite since `|0| = 0 < extension r` for any `r > 0`
    use 1
    simp [extension]

  neg_mem := by
    -- If `x` is finite, then `-x` is finite because `|-x| = |x|`
    intro x hx
    obtain ⟨r, hr⟩ := hx
    use r
    simp [abs_neg]
    exact hr

  add_mem := by
    -- Closure under addition follows from `galaxy_zero_subring`
    intro x y hx hy
    exact (galaxy_zero_subring x y hx hy).1

  mul_mem := by
    -- Closure under multiplication follows from `galaxy_zero_subring`
    intro x y hx hy
    exact (galaxy_zero_subring x y hx hy).2.2

  one_mem := by
    -- `1` is finite since `|1| = 1 < extension 2`
    use 2
    simp [extension]

  sub_mem := by
    -- Closure under subtraction follows from `galaxy_zero_subring`
    intro x y hx hy
    exact (galaxy_zero_subring x y hx hy).2.1

lemma finite_sub_closed {x y : R*} (hx : finite x) (hy : finite y) : finite (x - y) :=
  (galaxy_zero_subring x y hx hy).2.1

lemma extension_add (a b : ℝ) : extension (a + b) = extension a + extension b :=
  map_add extension a b

open Classical

open Set -- ne_empty_iff_nonempty / nonempty_iff_ne_empty  s ≠ ∅ ↔ s.Nonempty

-- def finite  (x : R*) : Prop := ∃ r : ℝ, |x| < extension r

lemma finite_add {x y : R*} (hx : finite x) (hy : finite y) : finite (x + y) :=
  (galaxy_zero_subring x y hx hy).1

@[simp]
lemma finite_sub_symm (x y : R*) : finite (x - y) ↔ finite (y - x) :=
  by rw [finite, finite, abs_sub_comm]


@[simp]
lemma finite_sub_symm2 (x y : R*) : finite (x - y) ↔ finite (y - x) :=
  by
    constructor
    · intro h
      obtain ⟨r, hr⟩ := h
      -- have hr : |x - y| < extension r
      have h1 : |x - y| = |y - x| := by rw [abs_sub_comm]
      rw [h1] at hr
      exact ⟨r, hr⟩
    · intro h
      obtain ⟨r, hr⟩ := h
      -- have hr : |y - x| < extension r
      have h2 :  |y - x| = |x - y| := by rw [abs_sub_comm]
      rw [h2] at hr
      exact ⟨r, hr⟩

-- lemma finite_sub_symm {x y : R*} : finite (x - y) ↔ finite (y - x) :=
-- by
--   have hxy := λ h : finite (x - y), finite_sub_closed h h -- Use finite properties
--   exact ⟨hxy, hxy⟩

lemma ne_empty_iff_nonempty {α : Type*} {s : Set α} : s ≠ ∅ ↔ s.Nonempty :=
  nonempty_iff_ne_empty.symm


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
    -- sorry
    exact subset_contradiction (Set.inter_subset_left _ _) (Set.inter_subset_right _ _) hz


theorem galaxy_inter_eq2 : ∀ x y : R*, (galaxy x ∩ galaxy y) ≠ ∅ → galaxy x = galaxy y :=
by
  intros x y h_nonempty
  have h_nonempty' : (galaxy x ∩ galaxy y).Nonempty := ne_empty_iff_nonempty.mp h_nonempty
  obtain ⟨w, hw⟩ := h_nonempty' -- Extract an element from the intersection
  dsimp [galaxy] at hw -- Unfold the definition of `galaxy`
  have h_finite_xw : finite (x - w) := hw.1
  have h_finite_yw : finite (y - w) := hw.2
  have h_finite_wy : finite (w - y) := (finite_sub_symm y w).mp h_finite_yw
  have h_finite_wx : finite (w - x) := (finite_sub_symm x w).mp h_finite_xw
  ext z
  simp only [galaxy, Set.mem_setOf_eq]
  constructor
  · intro hz
    -- Explicit rewrite before applying `finite_add`
    have h_xz : x - z = (x - y) + (y - z) := by ring
    have h_wz : w - z = (w - y) + (y - z) := by ring
    rw [h_xz] at hz
    have h_finite_wz : finite ((w - y) + (y - z)) := finite_add h_finite_wy hz
    exact h_finite_wz
  · intro hz
    have h_wz : w - z = (w - x) + (x - z) := by ring
    rw [h_wz]
    have h_finite_wz : finite ((w - x) + (x - z)) := finite_add h_finite_wx hz
    exact h_finite_wz


theorem galaxy_inter_eq : ∀ x y : R*, (galaxy x ∩ galaxy y) ≠ ∅ → galaxy x = galaxy y :=
by
  intros x y h_nonempty
  have h_nonempty' : (galaxy x ∩ galaxy y).Nonempty := (ne_empty_iff_nonempty.mp h_nonempty)
  obtain ⟨w, hw⟩ := h_nonempty' -- Extract an element from the intersection
  dsimp [galaxy] at hw -- Unfold the definition of `galaxy`
  have h_welem : w ∈ {k | finite (x - k)} := hw.1
  have h_welem2 : w ∈ {k | finite (y - k)} := hw.2
  have h_finite_xw : finite (x - w) := by simp at h_welem; exact h_welem
  have h_finite_yw : finite (y - w) := by simp at h_welem2; exact h_welem2
  have h_finite_wy : finite (w - y) := (finite_sub_symm y w).mp h_finite_yw
  have h_finite_wx : finite (w - x) := (finite_sub_symm x w).mp h_finite_xw
  ext z
  simp only [galaxy, Set.mem_setOf_eq]
  constructor
  · intro hz
--  finite (x - z) => |x - z| < extension r for some r
-- |y - z| = |y - w + w - z| ≤ |y - w| + |w - z| < extension r + extension r = 2 * extension r
-- |y - z| = |y - w + w - z| ≤ |y - w| + |w - x + x - z| ≤ |y - w| + |w - x | + | x - z|
-- |y - z| <= finite +  finite + finite
-- => finite (y - z) QE
    show finite (y - z)
    obtain ⟨r_xz, hr1⟩ := hz
    obtain ⟨r_yw, hr2⟩ := h_finite_yw
    obtain ⟨r_wx, hr3⟩ := h_finite_wx
    have h_bound : |y - z| < extension (r_wx + r_yw + r_xz) :=
    calc
      |y - z| = |(y - w) + (w - z)|   := by rw [←sub_add_sub_cancel y w z]
      _ ≤ |y - w| + |w - z|           := abs_add (y - w) (w - z)
      _ = |y - w| + |(w - x) + (x - z)| := by rw [←sub_add_sub_cancel w x z]
      _ ≤ |y - w| + (|w - x| + |x - z|) := by exact add_le_add_left (abs_add (w - x) (x - z)) _
      _ < extension r_yw + (extension r_wx + extension r_xz) := add_lt_add hr2 (add_lt_add hr3 hr1)
      -- _ = extension (r_yw + r_wx + r_xz) := by rw [extension_add, extension_add]
      _ = extension (r_wx + r_yw + r_xz) := by rw [extension_add, extension_add]
    exact ⟨r_wx + r_yw + r_xz, h_bound⟩
  · intro hz
    have h_finite_wz : finite (w - z) := finite_add h_finite_wy hz
    have h_finite_xz : finite (x - z) := finite_add h_finite_xw h_finite_wz
    exact h_finite_xz

theorem galaxy_inter_eq : ∀ x y : R*, galaxy x ∩ galaxy y ≠ ∅ → galaxy x = galaxy y :=
  λ x y h_nonempty => by
    obtain ⟨w, hw⟩ := Set.nonempty_def.mp h_nonempty
    have h_finite_wx : finite (w - x) := hw.1
    have h_finite_wy : finite (w - y) := hw.2

theorem galaxy_inter_eq22 : ∀ x y : R*, (galaxy x ∩ galaxy y).Nonempty → galaxy x = galaxy y :=
fun x y h_nonempty =>
  let ⟨z, hz⟩ := h_nonempty -- Extract an element `z` from the intersection
  have h_finite_xz : finite (x - z) := hz.1
  have h_finite_yz : finite (y - z) := hz.2
  have h_finite_xy : finite (x - y) :=
    by
      have h : x - y = (x - z) - (y - z) := by ring
      sorry -- rw h
      -- exact galaxy_zero_subring _ _ h_finite_xz h_finite_yz

  Set.ext fun w => ⟨
    -- Forward direction: If w is in galaxy x, show it's in galaxy y
    fun hw =>
      -- have h_finite_wx : finite (x - w) := hw
      have h_finite_wx : finite (w - x) := hw
      have h_finite_wy : finite (w - y) :=
        by
          have h : w - y = (w - x) + (x - y) := by ring
          sorry -- rw h
          -- exact galaxy_zero_subring _ _ h_finite_wx h_finite_xy
      h_finite_wy,

    -- Reverse direction: If w is in galaxy y, show it's in galaxy x
    fun hw =>
      have h_finite_wy : finite (w - y) := hw
      have h_finite_wx : finite (w - x) :=
        by
          have h : w - x = (w - y) - (x - y) := by ring
          sorry -- rw h
          -- exact galaxy_zero_subring _ _ h_finite_wy h_finite_xy
      h_finite_wx
  ⟩

theorem galaxy_inter_eq : ∀ x y : R*, (galaxy x ∩ galaxy y).Nonempty → galaxy x = galaxy y :=
fun x y h_nonempty =>
  let ⟨z, hz⟩ := h_nonempty
  have h_finite_xz : finite (x - z) := hz.1
  have h_finite_yz : finite (y - z) := hz.2
  have h_finite_xy : finite (x - y) :=
    have h := (x - z) - (y - z)
    Eq.subst h (galaxy_zero_subring _ _ h_finite_xz h_finite_yz)
  Set.ext fun w =>
    ⟨fun hw =>
      have h_finite_wx : finite (w - x) :=
        have h := (w - y) + (y - z) + (z - x)
        Eq.subst h (galaxy_zero_subring _ _ (galaxy_zero_subring _ _ hw h_finite_yz).1 h_finite_xz)
      h_finite_wx,
    fun hw =>
      have h_finite_wy : finite (w - y) :=
        have h := (w - x) + (x - z) + (z - y)
        Eq.subst h (galaxy_zero_subring _ _ (galaxy_zero_subring _ _ hw h_finite_xz).1 h_finite_yz)
      h_finite_wy⟩

fun x y h_nonempty =>
  let ⟨z, hz⟩ := Set.nonempty_def.mp h_nonempty
  have h_finite_xz : finite (x - z) := hz.1
  have h_finite_yz : finite (y - z) := hz.2
  have h_finite_xy : finite ((x - z) - (y - z)) :=
    galaxy_zero_subring _ _ h_finite_xz h_finite_yz
  funext fun w =>
    propext ⟨
      fun hw =>
        have h_finite_wx : finite (w - x) :=
          let h := (w - y) + (y - z) + (z - x)
          Eq.trans h.symm (galaxy_zero_subring _ _ (galaxy_zero_subring _ _ hw h_finite_yz).1 h_finite_xz)
        h_finite_wx,
      fun hw =>
        have h_finite_wy : finite (w - y) :=
          let h := (w - x) + (x - z) + (z - y)
          Eq.trans h.symm (galaxy_zero_subring _ _ (galaxy_zero_subring _ _ hw h_finite_xz).1 h_finite_yz)
        h_finite_wy
    ⟩

theorem galaxy_inter_eq : ∀ x y : R*, galaxy x ∩ galaxy y ≠ ∅ → galaxy x = galaxy y :=
by {
  intros x y h_nonempty,
  obtain ⟨z, hz⟩ := set.nonempty_def.mp h_nonempty,
  have h_finite_xz : finite (x - z) := hz.1,
  have h_finite_yz : finite (y - z) := hz.2,
  have h_finite_xy : finite ((x - z) - (y - z)),
  { simp only [sub_sub_sub_cancel_right],
    exact galaxy_zero_subring _ _ h_finite_xz h_finite_yz, },
  ext w,
  simp only [galaxy, set.mem_set_of_eq],
  split,
  { intro hw,
    have h_finite_wx : finite (w - x),
    { have : (w - y) + (y - z) + (z - x) = w - x,
      { ring, },
      rw ← this,
      exact galaxy_zero_subring _ _ (galaxy_zero_subring _ _ hw h_finite_yz).1 h_finite_xz, },
    exact h_finite_wx, },
  { intro hw,
    have h_finite_wy : finite (w - y),
    { have : (w - x) + (x - z) + (z - y) = w - y,
      { ring, },
      rw ← this,
      exact galaxy_zero_subring _ _ (galaxy_zero_subring _ _ hw h_finite_xz).1 h_finite_yz, },
    exact h_finite_wy, },
}

theorem galaxy_inter_eq : ∀ x y : R*, galaxy x ∩ galaxy y ≠ ∅ → galaxy x = galaxy y :=
-- theorem galaxy_inter_eq (x y : R*) (h_nonempty : (galaxy x ∩ galaxy y).Nonempty) :
  -- galaxy x = galaxy y := by
  -- obtain ⟨z, hz⟩ := h_nonempty
  unfold galaxy at *
  ext w
  constructor
  · intro hwx
    have hzx : finite (x - z) := hz.1
    have hzy : finite (y - z) := hz.2
    show finite (w - z)

    -- Show that w - z is finite
    have hwx_z : finite ((w - x) + (x - z)) := finite_add hwx hzx
    have hwz : finite (w - z) :=
      calc
        w - z = (w - x) + (x - z) := by ring
        _ : finite := hwx_z
        -- _    : finite := finite_add hwx hzx
    have h : finite ((w - z) - (y - z)) :=
      calc
        (w - z) - (y - z) = w - y := by ring
        _ : finite := finite_sub hwz hzy
    exact h
  · intro hwy
    have hzx : finite (x - z) := hz.1
    have hzy : finite (y - z) := hz.2
    have hwz : finite (w - z) :=
      calc
        w - z = (w - y) + (y - z) := by ring
        _    : finite := finite_add hwy hzy
    have h : finite ((w - z) - (x - z)) :=
      calc
        (w - z) - (x - z) = w - x := by ring
        _ : finite := finite_sub hwz hzx
    exact h

theorem galaxy_inter_eq (x y : R*) (h_nonempty : (galaxy x ∩ galaxy y).Nonempty) :
  galaxy x = galaxy y := by
  obtain ⟨z, hz⟩ := h_nonempty
  unfold galaxy at *
  ext w
  constructor
  · intro hwx
    have hzx : finite (x - z) := hz.1
    have hzy : finite (y - z) := hz.2
    have h : finite ((w - x) + (x - z) + (z - y)) := finite_add (finite_add hwx hzx) hzy
    rw [←sub_add_sub_cancel w x z, ←sub_add_sub_cancel z y x] at h
    exact h
  · intro hwy
    have hzx : finite (x - z) := hz.1
    have hzy : finite (y - z) := hz.2
    have h : finite ((w - y) + (y - z) + (z - x)) := finite_add (finite_add hwy hzy) hzx
    rw [←sub_add_sub_cancel w y z, ←sub_add_sub_cancel z x y] at h
    exact h

theorem galaxy_inter_eq (x y : R*) (h_nonempty : (galaxy x ∩ galaxy y).Nonempty) :
  galaxy x = galaxy y := by
  obtain ⟨z, hz⟩ := h_nonempty
  unfold galaxy at *
  ext w
  constructor
  · intro hwx
    have hzx : finite (x - z) := hz.1
    have hzy : finite (y - z) := hz.2
    have h : finite (w - y) := finite_add (finite_add hwx hzx) hzy
    exact h
  · intro hwy
    have hzx : finite (x - z) := hz.1
    have hzy : finite (y - z) := hz.2
    have h : finite (w - x) := finite_add (finite_add hwy hzy) hzx
    exact h

    -- Since z ∈ galaxy x, we have finite (z - x)
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
