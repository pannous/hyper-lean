/-
  Algebraic probability on the concrete HyperList backend.

  Probabilities are derived directly from favorable and total hyperfinite
  algebraic counts.  HyperList represents finite Laurent polynomials.  Its
  concrete addition and multiplication are exact, but a multiplicative
  inverse is exact only for one nonzero monomial.  The API therefore makes a
  nonzero monomial denominator explicit instead of offering unrestricted
  division of mixed-order expressions.
-/
import Hyper.HyperList

namespace Hypers
namespace HyperLists
namespace AlgebraicProbability

/-- Equality of algebraic values, expressed without relying on raw list order
or on the aspirational `Field R*` instance. -/
def AlgebraicallyEqual (x y : R*) : Prop :=
  ∀ order : ℚ, coeffAt x order = coeffAt y order

infix:50 " ≡ₐ " => AlgebraicallyEqual

/-- A canonical monomial `coefficient * omega^order`. -/
def monomial (coefficient : 𝔽) (order : ℚ) : R* :=
  if coefficient = 0 then 0 else [(coefficient, order)]

@[simp] theorem monomial_zero (order : ℚ) : monomial 0 order = 0 := by
  simp [monomial]

theorem monomial_of_ne {coefficient : 𝔽} {order : ℚ}
    (h : coefficient ≠ 0) :
    monomial coefficient order = ([(coefficient, order)] : R*) := by
  simp [monomial, h]

@[simp] theorem monomial_one_zero : monomial 1 0 = one := by
  simp [monomial, one]

@[simp] theorem monomial_one_one : monomial 1 1 = ω := by
  simp [monomial, omega]

@[simp] theorem monomial_one_neg_one : monomial 1 (-1) = ε := by
  simp [monomial, epsilon]

/-- A hyperfinite algebraic count.  Positive `order` denotes an omega-order
count; negative `order` records finer-than-unit rarity. -/
structure Count where
  coefficient : 𝔽
  order : ℚ
deriving DecidableEq, Repr

namespace Count

def value (count : Count) : R* := monomial count.coefficient count.order

@[simp] theorem value_mk (coefficient : 𝔽) (order : ℚ) :
    (Count.mk coefficient order).value = monomial coefficient order := rfl

end Count

/-- A count suitable as a denominator.  The proof field prevents division by
zero and records exactly the fragment where reciprocal monomials are exact. -/
structure NonzeroCount extends Count where
  coefficient_ne_zero : coefficient ≠ 0

namespace NonzeroCount

def value (count : NonzeroCount) : R* := count.toCount.value

def reciprocalValue (count : NonzeroCount) : R* :=
  monomial count.coefficient⁻¹ (-count.order)

end NonzeroCount

/-- Probability obtained from favorable and total algebraic counts. -/
def probability (favorable : Count) (total : NonzeroCount) : R* :=
  monomial
    (favorable.coefficient * total.coefficient⁻¹)
    (favorable.order - total.order)

/-- The complementary event has algebraic probability `1 - p`, computed with
the concrete normalized operations. -/
def complement (p : R*) : R* := fieldAdd one (fieldNeg p)

/-- Conjunction of events declared independent by the model. -/
def independentAnd (p q : R*) : R* := fieldMul p q

/-- Conditional probability `P(A and B) / P(B)`, where `P(B)` is explicitly a
nonzero monomial count and hence has an exact reciprocal in this backend. -/
def conditional (joint : R*) (given : NonzeroCount) : R* :=
  fieldMul joint given.reciprocalValue

/-- Expected value of a finite list of `(value, probability)` pairs. -/
def expectation : List (R* × R*) → R*
  | [] => 0
  | (value, chance) :: rest =>
      fieldAdd (fieldMul value chance) (expectation rest)

theorem monomial_mul {c d : 𝔽} {i j : ℚ}
    (hc : c ≠ 0) (hd : d ≠ 0) :
    fieldMul (monomial c i) (monomial d j) = monomial (c * d) (i + j) := by
  rw [monomial_of_ne hc, monomial_of_ne hd,
    monomial_of_ne (mul_ne_zero hc hd)]
  show normalize (([(c, i)] : List (𝔽 × ℚ)).product [(d, j)] |>.map _) = _
  simp [normalize, simplify, mergeAdjacent, List.product, mul_ne_zero hc hd]

/-- The computational ratio agrees with multiplication by the exact reciprocal
when the favorable count is also nonzero. -/
theorem probability_eq_ratio (favorable : Count) (total : NonzeroCount)
    (hf : favorable.coefficient ≠ 0) :
    probability favorable total =
      fieldMul favorable.value total.reciprocalValue := by
  rcases favorable with ⟨f, i⟩
  rcases total with ⟨⟨t, j⟩, ht⟩
  unfold probability Count.value NonzeroCount.reciprocalValue
  rw [monomial_mul hf (inv_ne_zero ht)]
  congr 2
  ring

/-- The whole sample space normalizes to probability one. -/
theorem probability_total (total : NonzeroCount) :
    probability total.toCount total = one := by
  rcases total with ⟨⟨coefficient, order⟩, hcoefficient⟩
  unfold probability
  rw [show coefficient * coefficient⁻¹ = 1 from mul_inv_cancel₀ hcoefficient]
  have horder : order - order = 0 := by ring
  rw [horder, monomial_one_zero]

/-- Zero favorable outcomes have probability zero for every valid total. -/
theorem probability_zero (order : ℚ) (total : NonzeroCount) :
    probability ⟨0, order⟩ total = zero := by
  unfold probability monomial
  simp only [zero_mul]
  rfl

/-- A denominator count cancels with its explicitly constructed reciprocal. -/
theorem count_mul_reciprocal (count : NonzeroCount) :
    fieldMul count.value count.reciprocalValue = one := by
  rcases count with ⟨⟨c, i⟩, hc⟩
  change fieldMul (monomial c i) (monomial c⁻¹ (-i)) = Hypers.one
  rw [monomial_mul hc (inv_ne_zero hc)]
  rw [show c * c⁻¹ = 1 from mul_inv_cancel₀ hc]
  have hi : i + -i = 0 := by ring
  rw [hi, monomial_one_zero]

theorem coeffAt_fieldNeg (p : R*) (order : ℚ) :
    coeffAt (fieldNeg p) order = -coeffAt p order := by
  unfold fieldNeg normalize
  rw [coeffAt_simplify, coeffAt_neg_map]

theorem coeffAt_one (order : ℚ) :
    coeffAt one order = if order = 0 then 1 else 0 := by
  by_cases h : order = 0
  · simp [one, coeffAt_cons, coeffAt_nil, h]
  · have h' : 0 ≠ order := fun hz => h hz.symm
    simp [one, coeffAt_cons, coeffAt_nil, h, h']

/-- Coefficient-level complement law, valid for arbitrary raw HyperLists. -/
theorem coeffAt_complement (p : R*) (order : ℚ) :
    coeffAt (complement p) order =
      (if order = 0 then 1 else 0) - coeffAt p order := by
  unfold complement
  rw [coeffAt_fieldAdd, coeffAt_one, coeffAt_fieldNeg]
  ring

/-- An event and its complement sum algebraically to certainty. -/
theorem event_complement_partition (p : R*) :
    fieldAdd p (complement p) ≡ₐ one := by
  intro order
  rw [coeffAt_fieldAdd, coeffAt_complement, coeffAt_one]
  ring

theorem independentAnd_coeff (p q : R*) (order : ℚ) :
    coeffAt (independentAnd p q) order =
      (p.map (fun term => term.1 * coeffAt q (order - term.2))).sum := by
  exact coeffAt_mul p q order

/-- Conditioning an independent conjunction on a nonzero monomial event
cancels algebraically, including when the conditioning event is infinitesimal. -/
theorem conditional_independent (given : NonzeroCount) (q : R*) :
    conditional (independentAnd given.value q) given ≡ₐ q := by
  rcases given with ⟨⟨c, i⟩, hc⟩
  intro order
  unfold conditional independentAnd NonzeroCount.value Count.value
    NonzeroCount.reciprocalValue
  rw [monomial_of_ne hc, monomial_of_ne (inv_ne_zero hc)]
  rw [coeffAt_mul_symm]
  simp only [List.map_singleton, List.sum_singleton]
  rw [coeffAt_mul]
  simp only [List.map_singleton, List.sum_singleton]
  have horder : order - -i - i = order := by ring
  rw [horder]
  field_simp

@[simp] theorem expectation_nil : expectation [] = 0 := rfl

@[simp] theorem expectation_cons (value chance : R*)
    (rest : List (R* × R*)) :
    expectation ((value, chance) :: rest) =
      fieldAdd (fieldMul value chance) (expectation rest) := rfl

theorem expectation_single (value chance : R*) :
    expectation [(value, chance)] ≡ₐ fieldMul value chance := by
  intro order
  rw [expectation_cons, expectation_nil, coeffAt_fieldAdd]
  change coeffAt (fieldMul value chance) order + coeffAt ([] : R*) order =
    coeffAt (fieldMul value chance) order
  rw [coeffAt_nil]
  ring

/-- A finite Bernoulli variable with outcomes zero and one has expected value
equal to its success probability. -/
theorem expectation_bernoulli (p : R*) :
    expectation [(zero, complement p), (one, p)] ≡ₐ p := by
  intro order
  simp only [expectation_cons, expectation_nil]
  rw [coeffAt_fieldAdd, coeffAt_fieldAdd]
  rw [coeffAt_mul, coeffAt_mul]
  simp [zero, one]
  change coeffAt ([] : R*) order = 0
  rw [coeffAt_nil]

/-- Finite expectations concatenate additively at every algebraic order. -/
theorem expectation_append (xs ys : List (R* × R*)) :
    expectation (xs ++ ys) ≡ₐ fieldAdd (expectation xs) (expectation ys) := by
  intro order
  induction xs with
  | nil =>
      simp only [List.nil_append, expectation_nil, coeffAt_fieldAdd]
      change coeffAt (expectation ys) order =
        coeffAt ([] : R*) order + coeffAt (expectation ys) order
      rw [coeffAt_nil]
      ring
  | cons outcome rest ih =>
      rcases outcome with ⟨value, chance⟩
      calc
        coeffAt (expectation (((value, chance) :: rest) ++ ys)) order =
            coeffAt (fieldMul value chance) order +
              coeffAt (expectation (rest ++ ys)) order := by
                rw [List.cons_append, expectation_cons, coeffAt_fieldAdd]
        _ = coeffAt (fieldMul value chance) order +
              (coeffAt (expectation rest) order + coeffAt (expectation ys) order) := by
                rw [ih, coeffAt_fieldAdd]
        _ = coeffAt
              (fieldAdd (expectation ((value, chance) :: rest)) (expectation ys)) order := by
                rw [coeffAt_fieldAdd, expectation_cons, coeffAt_fieldAdd]
                ring

-- Canonical gauging is executable in the concrete backend.
example : fieldMul epsilon omega = Hypers.one := by
  rw [show epsilon = monomial 1 (-1) from monomial_one_neg_one.symm,
    show omega = monomial 1 1 from monomial_one_one.symm,
    monomial_mul one_ne_zero one_ne_zero]
  norm_num

-- One favorable unit among `omega` algebraic trials has probability `epsilon`.
example :
    probability ⟨1, 0⟩ ⟨⟨1, 1⟩, one_ne_zero⟩ = ε := by
  change monomial (1 * (1 : 𝔽)⁻¹) (0 - 1) = epsilon
  norm_num

-- Rare-event cancellation: if `P(A) = epsilon` and `P(B) = 1/3`, then
-- `P(B and A) / P(A)` is algebraically `1/3`.
example :
    conditional
        (independentAnd ε (monomial (1 / 3) 0))
        ⟨⟨1, -1⟩, one_ne_zero⟩
      ≡ₐ monomial (1 / 3) 0 := by
  simpa using
    conditional_independent ⟨⟨1, -1⟩, one_ne_zero⟩ (monomial (1 / 3) 0)

-- An `omega`-sized payoff occurring with probability `epsilon` contributes 1.
example : expectation [(omega, epsilon)] ≡ₐ Hypers.one := by
  have hproduct : fieldMul omega epsilon = Hypers.one := by
    rw [show omega = monomial 1 1 from monomial_one_one.symm,
      show epsilon = monomial 1 (-1) from monomial_one_neg_one.symm,
      monomial_mul one_ne_zero one_ne_zero]
    norm_num
  intro order
  rw [expectation_cons, expectation_nil, hproduct, coeffAt_fieldAdd]
  change coeffAt Hypers.one order + coeffAt ([] : R*) order = coeffAt Hypers.one order
  rw [coeffAt_nil]
  ring

end AlgebraicProbability
end HyperLists
end Hypers
