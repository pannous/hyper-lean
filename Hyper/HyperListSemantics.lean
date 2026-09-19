import Hyper.HyperList
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.RingTheory.Localization.FractionRing

/-! Sound semantics for the original rational-exponent HyperList.
Only coefficient-preservation theorems from the legacy file are used.
Raw-list field instances are deliberately not used. -/
noncomputable section
namespace HyperListSemantics

abbrev Laurent := AddMonoidAlgebra ℚ ℚ

def interpret : Hypers.HyperList → Laurent
  | [] => 0
  | (c, e) :: xs => AddMonoidAlgebra.single e c + interpret xs

@[simp] theorem interpret_apply (xs : Hypers.HyperList) (e : ℚ) :
    interpret xs e = Hypers.coeffAt xs e := by
  induction xs with
  | nil => simp [interpret, Hypers.coeffAt_nil]
  | cons p xs ih =>
    rcases p with ⟨c, n⟩
    simp [interpret, Hypers.coeffAt_cons, ih, AddMonoidAlgebra.single_apply]

/-- Algebraic coefficient equality, not literal list equality. -/
theorem interpret_eq_iff (xs ys : Hypers.HyperList) :
    interpret xs = interpret ys ↔ ∀ e, Hypers.coeffAt xs e = Hypers.coeffAt ys e := by
  constructor
  · intro h e
    simpa using congrArg (fun p : Laurent => p e) h
  · intro h
    ext e
    simpa using h e

theorem interpret_simplify (xs : Hypers.HyperList) :
    interpret (Hypers.simplify xs) = interpret xs := by
  apply (interpret_eq_iff _ _).mpr
  exact Hypers.coeffAt_simplify xs

theorem interpret_add (xs ys : Hypers.HyperList) :
    interpret (Hypers.fieldAdd xs ys) = interpret xs + interpret ys := by
  ext e
  simpa using Hypers.coeffAt_fieldAdd xs ys e

theorem interpret_neg (xs : Hypers.HyperList) :
    interpret (Hypers.fieldNeg xs) = -interpret xs := by
  ext e
  simp only [interpret_apply, AddMonoidAlgebra.neg_apply]
  change Hypers.coeffAt (Hypers.simplify _) e = _
  rw [Hypers.coeffAt_simplify, Hypers.coeffAt_neg_map]

private theorem interpret_append (xs ys : Hypers.HyperList) :
    interpret (List.append xs ys) = interpret xs + interpret ys := by
  ext e
  simpa using Hypers.coeffAt_append xs ys e

private theorem interpret_shift (ys : Hypers.HyperList) (c n : ℚ) :
    interpret (ys.map fun p => (c * p.1, n + p.2)) =
      AddMonoidAlgebra.single n c * interpret ys := by
  induction ys with
  | nil => simp [interpret]
  | cons p ys ih =>
    rcases p with ⟨d, m⟩
    simp [interpret, ih, mul_add, AddMonoidAlgebra.single_mul_single]

private theorem interpret_convolution (xs ys : Hypers.HyperList) :
    interpret (xs.flatMap fun p => ys.map fun q => (p.1 * q.1, p.2 + q.2)) =
      interpret xs * interpret ys := by
  induction xs with
  | nil => simp [interpret]
  | cons p xs ih =>
    rcases p with ⟨c, n⟩
    change interpret (List.append (ys.map fun q => (c * q.1, n + q.2))
      (xs.flatMap fun p => ys.map fun q => (p.1 * q.1, p.2 + q.2))) = _
    rw [interpret_append, interpret_shift, ih]
    exact (add_mul _ _ _).symm

theorem interpret_mul (xs ys : Hypers.HyperList) :
    interpret (Hypers.fieldMul xs ys) = interpret xs * interpret ys := by
  rw [← interpret_convolution]
  apply (interpret_eq_iff _ _).mpr
  intro e
  rw [Hypers.coeffAt_mul, Hypers.coeffAt_flatMap]
  congr 1
  apply List.map_congr_left
  intro p _
  exact (Hypers.coeffAt_scale_shift ys p.1 p.2 e).symm

/-- The finite rational-power Laurent algebra has a genuine fraction field. -/
abbrev Exact := FractionRing Laurent

/-- This map identifies duplicate presentations; it is not injective on raw lists. -/
def exactValue (xs : Hypers.HyperList) : Exact := algebraMap Laurent Exact (interpret xs)

theorem exactValue_eq_iff (xs ys : Hypers.HyperList) :
    exactValue xs = exactValue ys ↔ ∀ e, Hypers.coeffAt xs e = Hypers.coeffAt ys e := by
  rw [exactValue, exactValue, (IsFractionRing.injective Laurent Exact).eq_iff]
  exact interpret_eq_iff xs ys

theorem exactValue_mul (xs ys : Hypers.HyperList) :
    exactValue (Hypers.fieldMul xs ys) = exactValue xs * exactValue ys := by
  simp [exactValue, interpret_mul]

end HyperListSemantics
