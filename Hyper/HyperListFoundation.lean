import Hyper.OrderedRational
import Mathlib.Algebra.Field.TransferInstance

/-! Exact integer-order HyperLists, interpreted as finite Laurent expressions.
A field value is a fraction of two lists, not generally a single list.
No legacy HyperList field instance or normalization axiom is imported. -/
noncomputable section
namespace HyperListFoundation

abbrev Terms (K : Type*) := List (K × ℤ)
variable {K : Type*} [Field K]

/-- The exponent is the power of ω, as in the original HyperList. -/
def eval : Terms K → RatFunc K
  | [] => 0
  | (c, n) :: xs => RatFunc.C c * RatFunc.X ^ n + eval xs

def add (a b : Terms K) : Terms K := a ++ b
def neg (a : Terms K) : Terms K := a.map fun (c, n) => (-c, n)
def mul (a b : Terms K) : Terms K :=
  a.flatMap fun (c, n) => b.map fun (d, m) => (c * d, n + m)

@[simp] theorem eval_nil : eval ([] : Terms K) = 0 := rfl
@[simp] theorem eval_single (c : K) (n : ℤ) :
    eval [(c, n)] = RatFunc.C c * RatFunc.X ^ n := by simp [eval]

@[simp] theorem eval_add (a b : Terms K) : eval (add a b) = eval a + eval b := by
  induction a with
  | nil => simp [add, eval]
  | cons p a ih =>
    rcases p with ⟨c, n⟩
    simpa [add, eval, add_assoc] using ih

@[simp] theorem eval_neg (a : Terms K) : eval (neg a) = -eval a := by
  induction a with
  | nil => simp [neg, eval]
  | cons p a ih =>
    rcases p with ⟨c, n⟩
    simp_all [neg, eval, neg_add_rev, add_comm]

private theorem eval_shift (b : Terms K) (c : K) (n : ℤ) :
    eval (b.map fun (d, m) => (c * d, n + m)) =
      (RatFunc.C c * RatFunc.X ^ n) * eval b := by
  induction b with
  | nil => simp [eval]
  | cons p b ih =>
    rcases p with ⟨d, m⟩
    simp only [List.map_cons, eval, map_mul, zpow_add₀ (RatFunc.X_ne_zero (K := K)), ih]
    ring

@[simp] theorem eval_mul (a b : Terms K) : eval (mul a b) = eval a * eval b := by
  induction a with
  | nil => simp [mul, eval]
  | cons p a ih =>
    rcases p with ⟨c, n⟩
    change eval (add (b.map fun (d, m) => (c * d, n + m)) (mul a b)) = _
    rw [eval_add, eval_shift, ih]
    simp [eval, add_mul]

/-- Equality is equality of values, never structural equality of raw lists. -/
def Equivalent (a b : Terms K) : Prop := eval a = eval b

/-- A polynomial has a finite-list presentation, including the zero polynomial. -/
def ofPolynomial (p : Polynomial K) : Terms K :=
  (List.range (p.natDegree + 1)).map fun n => (p.coeff n, (n : ℤ))

theorem eval_ofPolynomial (p : Polynomial K) :
    eval (ofPolynomial p) = algebraMap (Polynomial K) (RatFunc K) p := by
  have h (l : List ℕ) :
      eval (l.map fun n => (p.coeff n, (n : ℤ))) =
        (l.map fun n => RatFunc.C (p.coeff n) * RatFunc.X ^ n).sum := by
    induction l with
    | nil => rfl
    | cons n l ih => simp [eval, ih]
  rw [ofPolynomial, h]
  change (∑ n ∈ Finset.range (p.natDegree + 1), RatFunc.C (p.coeff n) * RatFunc.X ^ n) = _
  conv_rhs => rw [p.as_sum_range_C_mul_X_pow]
  simp

structure Fraction (K : Type*) [Field K] where
  numerator : Terms K
  denominator : Terms K
  denominator_ne_zero : eval denominator ≠ 0

namespace Fraction

def value (f : Fraction K) : RatFunc K := eval f.numerator / eval f.denominator

def ofValue (x : RatFunc K) : Fraction K where
  numerator := ofPolynomial x.num
  denominator := ofPolynomial x.denom
  denominator_ne_zero := by
    rw [eval_ofPolynomial]
    exact RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero x)

@[simp] theorem value_ofValue (x : RatFunc K) : (ofValue x).value = x := by
  simp only [value, ofValue, eval_ofPolynomial]
  exact RatFunc.num_div_denom x

/-- Every exact hyperreal used by the probability theory is two finite lists. -/
theorem value_surjective : Function.Surjective (value (K := K)) :=
  fun x => ⟨ofValue x, value_ofValue x⟩

def plus (f g : Fraction K) : Fraction K where
  numerator := add (mul f.numerator g.denominator) (mul g.numerator f.denominator)
  denominator := mul f.denominator g.denominator
  denominator_ne_zero := by simpa using mul_ne_zero f.denominator_ne_zero g.denominator_ne_zero

def times (f g : Fraction K) : Fraction K where
  numerator := mul f.numerator g.numerator
  denominator := mul f.denominator g.denominator
  denominator_ne_zero := by simpa using mul_ne_zero f.denominator_ne_zero g.denominator_ne_zero

/-- Reciprocal of a nonzero value swaps whole lists. -/
def reciprocal (f : Fraction K) (h : f.value ≠ 0) : Fraction K where
  numerator := f.denominator
  denominator := f.numerator
  denominator_ne_zero := by
    intro hz
    apply h
    simp [value, hz]

@[simp] theorem value_plus (f g : Fraction K) : (plus f g).value = f.value + g.value := by
  simp only [value, plus, eval_add, eval_mul]
  rw [div_add_div _ _ f.denominator_ne_zero g.denominator_ne_zero]
  ring

@[simp] theorem value_times (f g : Fraction K) : (times f g).value = f.value * g.value := by
  simp only [value, times, eval_mul, div_mul_div_comm]

@[simp] theorem value_reciprocal (f : Fraction K) (h : f.value ≠ 0) :
    (reciprocal f h).value = f.value⁻¹ := by simp [value, reciprocal]

theorem value_eq_iff_cross_multiply (f g : Fraction K) :
    f.value = g.value ↔
      Equivalent (mul f.numerator g.denominator) (mul g.numerator f.denominator) := by
  simp only [value, Equivalent, eval_mul]
  exact div_eq_div_iff f.denominator_ne_zero g.denominator_ne_zero

end Fraction

/-- Fraction presentations are identified by cross multiplication of values. -/
def fractionSetoid (K : Type*) [Field K] : Setoid (Fraction K) where
  r f g := f.value = g.value
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

abbrev Exact (K : Type*) [Field K] := Quotient (fractionSetoid K)

/-- The exact field is the quotient of finite-list fractions by value equality. -/
def exactEquiv : Exact K ≃ RatFunc K where
  toFun := Quotient.lift Fraction.value (fun _ _ h => h)
  invFun x := Quotient.mk _ (Fraction.ofValue x)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | _ f =>
      apply Quotient.sound
      exact Fraction.value_ofValue f.value
  right_inv := Fraction.value_ofValue

instance : Field (Exact K) := exactEquiv.field

/-- The quotient field addition agrees with explicit finite-list arithmetic. -/
theorem exact_plus (f g : Fraction K) :
    (Quotient.mk _ (Fraction.plus f g) : Exact K) = Quotient.mk _ f + Quotient.mk _ g := by
  apply exactEquiv.injective
  change (Fraction.plus f g).value = exactEquiv (exactEquiv.symm (f.value + g.value))
  rw [exactEquiv.apply_symm_apply]
  exact Fraction.value_plus f g

/-- The quotient field multiplication agrees with convolution of numerator/denominator lists. -/
theorem exact_times (f g : Fraction K) :
    (Quotient.mk _ (Fraction.times f g) : Exact K) = Quotient.mk _ f * Quotient.mk _ g := by
  apply exactEquiv.injective
  change (Fraction.times f g).value = exactEquiv (exactEquiv.symm (f.value * g.value))
  rw [exactEquiv.apply_symm_apply]
  exact Fraction.value_times f g

end HyperListFoundation
