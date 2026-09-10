import Hyper.AlgebraicProbability

/-!
  Rigorous algebraic cores for Exercises 15--20.

  Exercises 15, 16, 17, and 20 below are exact finite coefficient
  calculations.  The statements for Exercises 18 and 19 deliberately expose
  the extra hypotheses which a future hyperfinite/standard-part layer must
  provide.  In particular, this file does not use the unsound inverse of a
  multi-term `HyperList`, postulate transfer, or add axioms.
-/

namespace Hypers
namespace HyperLists
namespace AlgebraicStochasticsAdvanced

open AlgebraicProbability

/-- A raw monomial.  Unlike `AlgebraicProbability.monomial`, this also keeps
the zero-coefficient singleton; coefficient observations remain insensitive
to that representational detail. -/
def term (c e : ℚ) : R* := [(c, e)]

@[simp] theorem coeffAt_term (c e order : ℚ) :
    coeffAt (term c e) order = if e = order then c else 0 := by
  simp [term, coeffAt_cons, coeffAt_nil]

def linearEpsilon (constant slope : ℚ) : R* :=
  fieldAdd (term constant 0) (term slope (-1))

/-- Exact two-by-two convolution, kept explicit so it cannot accidentally use
the backend's invalid general inverse. -/
def twoByTwoProduct
    (a₀ a₁ e₀ e₁ b₀ b₁ f₀ f₁ : ℚ) : R* :=
  fieldAdd (term (a₀ * b₀) (e₀ + f₀)) <|
  fieldAdd (term (a₀ * b₁) (e₀ + f₁)) <|
  fieldAdd (term (a₁ * b₀) (e₁ + f₀))
    (term (a₁ * b₁) (e₁ + f₁))

def bernoulliVarianceNumerator (theta a : ℚ) : R* :=
  twoByTwoProduct theta a 0 (-1) (1 - theta) (-a) 0 (-1)

/-- Exercise 15: the Bernoulli variance numerator has exactly the advertised
constant coefficient. -/
theorem contamination_variance_constant (theta a : ℚ) :
    coeffAt
        (bernoulliVarianceNumerator theta a) 0 =
      theta * (1 - theta) := by
  simp [bernoulliVarianceNumerator, twoByTwoProduct,
    coeffAt_fieldAdd, coeffAt_term]

/-- Exercise 15: exact first infinitesimal coefficient. -/
theorem contamination_variance_linear (theta a : ℚ) :
    coeffAt
        (bernoulliVarianceNumerator theta a) (-1) =
      a * (1 - 2 * theta) := by
  simp [bernoulliVarianceNumerator, twoByTwoProduct,
    coeffAt_fieldAdd, coeffAt_term]
  ring

/-- Exercise 15: exact second infinitesimal coefficient. -/
theorem contamination_variance_quadratic (theta a : ℚ) :
    coeffAt
        (bernoulliVarianceNumerator theta a) (-2) =
      -a ^ 2 := by
  simp [bernoulliVarianceNumerator, twoByTwoProduct,
    coeffAt_fieldAdd, coeffAt_term]
  norm_num
  ring

/-- Dividing the three coefficients by a nonzero standard sample size gives
the variance expansion of Exercise 15.  This is standard scalar division,
not the general `HyperList` inverse. -/
theorem contamination_sample_mean_coefficients
    (theta a n : ℚ) (_hn : n ≠ 0) :
    let numerator := bernoulliVarianceNumerator theta a
    (coeffAt numerator 0 / n,
      coeffAt numerator (-1) / n,
      coeffAt numerator (-2) / n) =
    (theta * (1 - theta) / n,
      a * (1 - 2 * theta) / n,
      -(a ^ 2) / n) := by
  dsimp
  rw [contamination_variance_constant,
    contamination_variance_linear, contamination_variance_quadratic]

/-! ### Exercise 16: exact first-order likelihood coefficients -/

/-- Constant and linear coefficients of a finite polynomial. -/
structure FirstJet where
  constant : ℚ
  linear : ℚ
deriving DecidableEq, Repr

namespace FirstJet

def mul (x y : FirstJet) : FirstJet :=
  ⟨x.constant * y.constant,
    x.constant * y.linear + x.linear * y.constant⟩

def pow (x : FirstJet) : ℕ → FirstJet
  | 0 => ⟨1, 0⟩
  | n + 1 => mul (pow x n) x

theorem pow_one_plus (a : ℚ) : ∀ n : ℕ,
    pow ⟨1, a⟩ n = ⟨1, n * a⟩ := by
  intro n
  induction n with
  | zero => simp [pow]
  | succ n ih =>
      simp [pow, mul, ih]
      ring

end FirstJet

/-- The coefficient pair of the normalized likelihood ratio.  This is an
exact quotient of finite polynomials modulo terms divisible by epsilon². -/
def likelihoodFirstJet (q : ℚ) (successes failures : ℕ) : FirstJet :=
  FirstJet.mul
    (FirstJet.pow ⟨1, q⁻¹⟩ successes)
    (FirstJet.pow ⟨1, -(1 - q)⁻¹⟩ failures)

/-- Exercise 16: the first infinitesimal likelihood coefficient is the score
`s/q - f/(1-q)`, for arbitrary finite sample counts. -/
theorem likelihood_first_coefficient
    (q : ℚ) (successes failures : ℕ) :
    (likelihoodFirstJet q successes failures).linear =
      successes / q - failures / (1 - q) := by
  simp [likelihoodFirstJet, FirstJet.pow_one_plus, FirstJet.mul]
  ring

/-! ### Exercise 17: same-order Bayes cancellation -/

/-- Same-order cancellation is valid in any genuine field.  This theorem is
not instantiated with `R*`: its multi-term denominator does not have a finite
Laurent-polynomial inverse. -/
theorem bayes_same_order_cancel {K : Type*} [Field K]
    (epsilon c : K) (hepsilon : epsilon ≠ 0) :
    epsilon / (epsilon * (1 + c - c * epsilon)) =
      1 / (1 + c - c * epsilon) := by
  field_simp

/-- Multiplication by the Bayes denominator verifies the proposed series
through order two; the displayed cubic defect is exact. -/
theorem posterior_first_order_exact (c epsilon : ℚ) (hc : 1 + c ≠ 0) :
    ((1 + c) * epsilon - c * epsilon ^ 2) *
        (1 / (1 + c) + c / (1 + c) ^ 2 * epsilon) =
      epsilon - c ^ 2 / (1 + c) ^ 2 * epsilon ^ 3 := by
  field_simp
  ring

/-! ### Exercise 18: the honest infinite-exponent interface -/

/-- Everything needed from a future infinite-exponent implementation for the
extreme fair-coin test.  These are hypotheses, not an encoded transfer axiom. -/
structure ExtremePowerInterface (K : Type*) [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] where
  epsilon : K
  fairPowerAtOmega : K
  fairPower_pos : 0 < fairPowerAtOmega
  belowEveryStandardPower : ∀ k : ℕ, fairPowerAtOmega < epsilon ^ k

/-- Exercise 18 follows immediately once the analytic/hyperfinite layer has
actually supplied its positivity and growth comparison. -/
theorem extreme_test_conclusion {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K]
    (model : ExtremePowerInterface K) :
    0 < model.fairPowerAtOmega ∧
      ∀ k : ℕ, model.fairPowerAtOmega < model.epsilon ^ k :=
  ⟨model.fairPower_pos, model.belowEveryStandardPower⟩

/-! ### Exercise 19: algebraic Poisson core and standard-part interface -/

/-- Fixed-`k` part of the scaled hyperfinite binomial coefficient. -/
def scaledFallingFactorial {K : Type*} [Field K]
    (omega epsilon : K) (k : ℕ) : K :=
  (∏ i ∈ Finset.range k, (omega - i) * epsilon) / k.factorial

/-- Gauging rewrites every factor `(omega-i)*epsilon` as `1-i*epsilon`.
This is the exact algebraic content behind
`choose(omega,k) * epsilon^k ≃ 1/k!`. -/
theorem scaled_falling_factorial_gauged {K : Type*} [Field K]
    (omega epsilon : K) (gauge : omega * epsilon = 1) (k : ℕ) :
    scaledFallingFactorial omega epsilon k =
      (∏ i ∈ Finset.range k, (1 - (i : K) * epsilon)) / k.factorial := by
  unfold scaledFallingFactorial
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [sub_mul, gauge]

/-- Explicit contract for taking the standard coefficient of the two factors
in Exercise 19.  `leading` can later be instantiated by a genuine standard
part or constant-coefficient operation. -/
structure PoissonStandardInterface (K : Type*) [Field K] where
  leading : K → K
  lambda : K
  k : ℕ
  scaledChoose : K
  noSuccessPower : K
  probability : K
  exponential : K → K
  probability_factorization :
    probability = scaledChoose * lambda ^ k * noSuccessPower
  scaledChoose_leading : leading scaledChoose = 1 / k.factorial
  noSuccessPower_leading : leading noSuccessPower = 1 / exponential lambda
  leading_mul : ∀ x y, leading (x * y) = leading x * leading y
  leading_standard : ∀ x, leading (x ^ k) = x ^ k

/-- Exercise 19's Poisson coefficient, conditional only on the explicit
standard-coefficient laws above. -/
theorem poisson_standard_coefficient {K : Type*} [Field K]
    (model : PoissonStandardInterface K) :
    model.leading model.probability =
      model.lambda ^ model.k /
        (model.k.factorial * model.exponential model.lambda) := by
  rw [model.probability_factorization, model.leading_mul,
    model.leading_mul, model.scaledChoose_leading,
    model.leading_standard, model.noSuccessPower_leading]
  field_simp

/-! ### Exercise 20: exact coefficient cancellation -/

/-- The second-order Taylor polynomial for the success log factor, represented
at epsilon-orders `-1/2` and `-1`. -/
def successLogQuadratic (theta h : ℚ) : R* :=
  fieldAdd (term (h / theta) (-1 / 2))
    (term (-(h ^ 2) / (2 * theta ^ 2)) (-1))

/-- The corresponding failure log factor. -/
def failureLogQuadratic (theta h : ℚ) : R* :=
  fieldAdd (term (-h / (1 - theta)) (-1 / 2))
    (term (-(h ^ 2) / (2 * (1 - theta) ^ 2)) (-1))

def lanQuadraticLogRatio (theta h z sigma : ℚ) : R* :=
  fieldAdd
    (twoByTwoProduct theta (z * sigma) 1 (1 / 2)
      (h / theta) (-(h ^ 2) / (2 * theta ^ 2)) (-1 / 2) (-1))
    (twoByTwoProduct (1 - theta) (-(z * sigma)) 1 (1 / 2)
      (-h / (1 - theta)) (-(h ^ 2) / (2 * (1 - theta) ^ 2))
      (-1 / 2) (-1))

/-- The potentially infinite order-`sqrt(omega)` terms cancel exactly. -/
theorem lan_sqrtOmega_cancellation
    (theta h z sigma : ℚ) (htheta : theta ≠ 0)
    (hone : 1 - theta ≠ 0) :
    coeffAt (lanQuadraticLogRatio theta h z sigma) (1 / 2) = 0 := by
  norm_num [lanQuadraticLogRatio, twoByTwoProduct,
    coeffAt_fieldAdd, coeffAt_term]
  field_simp
  ring

/-- The finite coefficient of the quadratic LAN calculation.  The relation
`sigma^2=theta*(1-theta)` is passed explicitly; no square-root API is faked. -/
theorem lan_finite_coefficient
    (theta h z sigma : ℚ) (htheta : theta ≠ 0)
    (hone : 1 - theta ≠ 0) (hsigma : sigma ≠ 0)
    (hsigma_sq : sigma ^ 2 = theta * (1 - theta)) :
    coeffAt (lanQuadraticLogRatio theta h z sigma) 0 =
      h * z / sigma - h ^ 2 / (2 * sigma ^ 2) := by
  norm_num [lanQuadraticLogRatio, twoByTwoProduct,
    coeffAt_fieldAdd, coeffAt_term]
  field_simp
  rw [hsigma_sq]
  ring

/-- Honest boundary for a future logarithmic remainder proof: if the omitted
remainder has zero standard coefficient, it does not change the LAN result. -/
theorem lan_with_remainder_interface
    (quadratic remainder : R*) (answer : ℚ)
    (hquadratic : coeffAt quadratic 0 = answer)
    (hremainder : coeffAt remainder 0 = 0) :
    coeffAt (fieldAdd quadratic remainder) 0 = answer := by
  rw [coeffAt_fieldAdd, hquadratic, hremainder]
  norm_num

#print axioms contamination_sample_mean_coefficients
#print axioms likelihood_first_coefficient
#print axioms posterior_first_order_exact
#print axioms scaled_falling_factorial_gauged
#print axioms poisson_standard_coefficient
#print axioms lan_sqrtOmega_cancellation
#print axioms lan_finite_coefficient
#print axioms lan_with_remainder_interface

end AlgebraicStochasticsAdvanced
end HyperLists
end Hypers
