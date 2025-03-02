import Mathlib.Algebra.Order.CauSeq.BigOperators
import Mathlib.Data.Complex.Abs
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Nat.Choose.Sum

noncomputable section
theorem isCauSeq_exp (z : ℂ) : IsCauSeq abs fun n => ∑ m ∈ range n, z ^ m / m.factorial :=
  (isCauSeq_abs_exp z).of_abv

def hyper_exp' (z : ℂ) : CauSeq ℂ Complex.abs :=
  ⟨fun n => ∑ m ∈ range n, z ^ m / m.factorial, isCauSeq_exp z⟩

/-- The complex exponential function, defined via its Taylor series -/
def hyper_exp (z : 𝔽*) : 𝔽* :=
  CauSeq.lim (hyper_exp' z)

def sin (z : 𝔽*) : 𝔽* :=
  (exp (-z * I) - exp (z * I)) * I / 2
