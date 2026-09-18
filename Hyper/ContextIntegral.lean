import Hyper.OrderedRational

/-! Normalized algebraic integration on a finite observable partition.
An index names a region, not necessarily a single elementary outcome.
Its content may be infinite. There is no enumeration of ω objects.
The field, positivity, and total-content obligations are all checked. -/
noncomputable section
open scoped BigOperators
namespace AlgebraicIntegral

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {ι : Type*} [Fintype ι]

structure Context (K : Type*) (ι : Type*) [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [Fintype ι] where
  content : ι → K
  content_nonneg : ∀ i, 0 ≤ content i
  total_pos : 0 < ∑ i, content i

namespace Context
variable (Ω : Context K ι)

def total : K := ∑ i, Ω.content i
def raw (f : ι → K) : K := ∑ i, f i * Ω.content i
def integral (f : ι → K) : K := Ω.raw f / Ω.total

theorem total_ne_zero : Ω.total ≠ 0 := ne_of_gt Ω.total_pos

@[simp] theorem integral_one : Ω.integral (fun _ => 1) = 1 := by
  simp [integral, raw, total, ne_of_gt Ω.total_pos]

@[simp] theorem integral_zero : Ω.integral (fun _ => 0) = 0 := by
  simp [integral, raw]

theorem integral_add (f g : ι → K) :
    Ω.integral (fun i => f i + g i) = Ω.integral f + Ω.integral g := by
  simp [integral, raw, add_mul, Finset.sum_add_distrib, add_div]

theorem integral_scale (a : K) (f : ι → K) :
    Ω.integral (fun i => a * f i) = a * Ω.integral f := by
  simp [integral, raw, mul_assoc, ← Finset.mul_sum, mul_div_assoc]

theorem integral_const (a : K) : Ω.integral (fun _ => a) = a := by
  simpa using Ω.integral_scale a (fun _ => 1)

theorem integral_nonneg {f : ι → K} (hf : ∀ i, 0 ≤ f i) : 0 ≤ Ω.integral f :=
  div_nonneg (Finset.sum_nonneg (fun i _ => mul_nonneg (hf i) (Ω.content_nonneg i)))
    Ω.total_pos.le

theorem integral_mono {f g : ι → K} (h : ∀ i, f i ≤ g i) :
    Ω.integral f ≤ Ω.integral g := by
  apply div_le_div_of_nonneg_right _ Ω.total_pos.le
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (h i) (Ω.content_nonneg i))

section Events
variable [DecidableEq ι]

def indicator (E : Finset ι) (i : ι) : K := if i ∈ E then 1 else 0
def prob (E : Finset ι) : K := Ω.integral (indicator E)

@[simp] theorem prob_univ : Ω.prob Finset.univ = 1 := by
  have h : (indicator (Finset.univ : Finset ι) : ι → K) = fun _ => 1 := by
    funext i
    simp [indicator]
  rw [prob, h, integral_one]

@[simp] theorem prob_empty : Ω.prob ∅ = 0 := by
  have h : (indicator (∅ : Finset ι) : ι → K) = fun _ => 0 := by
    funext i
    simp [indicator]
  rw [prob, h, integral_zero]

theorem prob_nonneg (E : Finset ι) : 0 ≤ Ω.prob E := by
  apply Ω.integral_nonneg
  intro i
  simp only [indicator]
  split_ifs <;> positivity

theorem prob_mono {E F : Finset ι} (h : E ⊆ F) : Ω.prob E ≤ Ω.prob F := by
  apply Ω.integral_mono
  intro i
  simp only [indicator]
  split_ifs with he hf hf
  · rfl
  · exact False.elim (hf (h he))
  · exact zero_le_one
  · rfl

theorem prob_le_one (E : Finset ι) : Ω.prob E ≤ 1 := by
  simpa using Ω.prob_mono (Finset.subset_univ E)

theorem prob_union_inter (E F : Finset ι) :
    Ω.prob (E ∪ F) + Ω.prob (E ∩ F) = Ω.prob E + Ω.prob F := by
  rw [prob, prob, ← integral_add, prob, prob, ← integral_add]
  congr 1
  funext i
  simp only [indicator, Finset.mem_union, Finset.mem_inter]
  by_cases he : i ∈ E <;> by_cases hf : i ∈ F <;> simp [he, hf]

theorem prob_compl (E : Finset ι) : Ω.prob Eᶜ = 1 - Ω.prob E := by
  have h := Ω.prob_union_inter E Eᶜ
  simp at h
  linear_combination -h

theorem prob_disjoint_union {E F : Finset ι} (h : Disjoint E F) :
    Ω.prob (E ∪ F) = Ω.prob E + Ω.prob F := by
  simpa [Finset.disjoint_iff_inter_eq_empty.mp h] using Ω.prob_union_inter E F

theorem prob_singleton (i : ι) :
    Ω.prob {i} = Ω.content i / Ω.total := by
  classical
  simp [prob, integral, raw, indicator]

/-- Integrate over E in the unchanged ambient context Ω. -/
def restricted (E : Finset ι) (f : ι → K) : K :=
  Ω.integral (fun i => indicator E i * f i)

/-- This changes context to E; nonzero probability is a theorem hypothesis
for its normalization and reproducing laws, never silently assumed. -/
def conditional (E : Finset ι) (f : ι → K) : K := Ω.restricted E f / Ω.prob E

theorem conditional_one {E : Finset ι} (hE : Ω.prob E ≠ 0) :
    Ω.conditional E (fun _ => 1) = 1 := by
  simpa [conditional, restricted, prob] using div_self hE

/-- A support-normalized spike. Its coefficient depends on Ω and E. -/
def delta (E : Finset ι) (i : ι) : K := (Ω.prob E)⁻¹ * indicator E i

theorem integral_delta {E : Finset ι} (hE : Ω.prob E ≠ 0) :
    Ω.integral (Ω.delta E) = 1 := by
  change Ω.integral (fun i => (Ω.prob E)⁻¹ * indicator E i) = 1
  rw [integral_scale]
  exact inv_mul_cancel₀ hE

/-- On an arbitrary support a spike reproduces the conditional average. -/
theorem delta_average (E : Finset ι) (f : ι → K) :
    Ω.integral (fun i => f i * Ω.delta E i) = Ω.conditional E f := by
  have heq : (fun i => f i * Ω.delta E i) =
      (fun i => (Ω.prob E)⁻¹ * (indicator E i * f i)) := by
    funext i
    simp [delta]
    ring
  rw [heq, integral_scale]
  simp [conditional, restricted, div_eq_mul_inv, mul_comm]

/-- A genuine singleton support reproduces evaluation exactly. -/
theorem delta_singleton (i : ι) (hi : Ω.content i ≠ 0)
    (f : ι → K) : Ω.integral (fun j => f j * Ω.delta {i} j) = f i := by
  classical
  rw [delta_average]
  simp [conditional, restricted, integral, raw, indicator, prob_singleton]
  field_simp [hi, Ω.total_ne_zero]

end Events

/-- Scaling all contents leaves the normalized integral unchanged. -/
theorem scale_invariant (a : K) (ha : a ≠ 0) (f : ι → K) :
    (∑ i, f i * (a * Ω.content i)) / (∑ i, a * Ω.content i) = Ω.integral f := by
  simp_rw [show ∀ i, f i * (a * Ω.content i) = a * (f i * Ω.content i) by
    intro i; ring]
  rw [← Finset.mul_sum, ← Finset.mul_sum, mul_div_mul_left _ _ ha]
  rfl

/-- A compatible subdivision preserves every old observable exactly. -/
theorem refinement_invariant {κ : Type*} [Fintype κ]
    (Λ : Context K (ι × κ)) (h : ∀ i, ∑ j, Λ.content (i, j) = Ω.content i)
    (f : ι → K) : Λ.integral (fun ij => f ij.1) = Ω.integral f := by
  simp only [integral, raw, total, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, h]

/-- Any nonnegative density with positive raw integral defines a context. -/
def withDensity (p : ι → K) (hp : ∀ i, 0 ≤ p i) (ht : 0 < Ω.raw p) : Context K ι where
  content i := p i * Ω.content i
  content_nonneg i := mul_nonneg (hp i) (Ω.content_nonneg i)
  total_pos := ht

theorem withDensity_integral (p : ι → K) (hp : ∀ i, 0 ≤ p i)
    (ht : 0 < Ω.raw p) (f : ι → K) :
    (Ω.withDensity p hp ht).integral f =
      Ω.integral (fun i => f i * p i) / Ω.integral p := by
  simp only [integral, raw, total, withDensity, mul_assoc]
  rw [div_div_div_cancel_right₀ (ne_of_gt Ω.total_pos)]

section Product
variable {κ : Type*} [Fintype κ] (Λ : Context K κ)

def product : Context K (ι × κ) where
  content ij := Ω.content ij.1 * Λ.content ij.2
  content_nonneg ij := mul_nonneg (Ω.content_nonneg _) (Λ.content_nonneg _)
  total_pos := by
    rw [Fintype.sum_prod_type, ← Finset.sum_mul_sum]
    exact mul_pos Ω.total_pos Λ.total_pos

theorem product_total : (Ω.product Λ).total = Ω.total * Λ.total := by
  simp [total, product, Fintype.sum_prod_type, Finset.sum_mul_sum]

/-- Finite algebraic Fubini, including all infinitesimal terms. -/
theorem fubini (f : ι × κ → K) :
    (Ω.product Λ).integral f = Ω.integral (fun i => Λ.integral (fun j => f (i, j))) := by
  unfold integral
  rw [product_total]
  simp only [raw, product, Fintype.sum_prod_type]
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div, Finset.sum_mul]
  have h : (∑ i, ∑ j, f (i, j) * (Ω.content i * Λ.content j)) =
      ∑ i, ∑ j, f (i, j) * Λ.content j * Ω.content i := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h]
  ring

end Product
end Context

/- Explicit ambient context prevents silently renormalizing each event. -/
scoped notation:70 "∫[" Ω "] " f:71 => Context.integral Ω f
scoped notation:70 "∫[" Ω "; " E "] " f:71 => Context.restricted Ω E f
scoped notation:70 "∫[" Ω " | " E "] " f:71 => Context.conditional Ω E f
end AlgebraicIntegral
