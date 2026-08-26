import Hyper.PiEField
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

/-!
First isolated step toward a genuinely computable `ℚ(X,Y)` fraction field.

The runtime carrier is the existing executable sparse-list normal form.  For
proofs only, `toGroupAlgebra` interprets it in Mathlib's group algebra
`ℚ[ℚ × ℚ]`, which is known to have no zero divisors.  Two small certification
axioms currently connect the executable normalizer to that proof model.  They
are the exact proof obligations to replace with a leading-term argument; the
field API and runtime representation will not change when they are proved.

This experiment deliberately lives outside `PiEField.lean` and is not selected
as the active coefficient backend yet.
-/

namespace ComputableFractionAttempt

/-- Sparse Laurent polynomials whose stored list is in canonical form. -/
structure PolyNF where
  terms : PiEField
  normalized : PiEField.simplify terms = terms

instance : DecidableEq PolyNF := fun a b =>
  if h : a.terms = b.terms then isTrue (by cases a; cases b; simp_all)
  else isFalse (fun hab => h (congrArg PolyNF.terms hab))

/-- The one normalization fact needed to close every executable constructor. -/
axiom simplify_idempotent (p : PiEField) :
  PiEField.simplify (PiEField.simplify p) = PiEField.simplify p

def normalize (p : PiEField) : PolyNF :=
  ⟨PiEField.simplify p, simplify_idempotent p⟩

instance : Zero PolyNF := ⟨normalize 0⟩
instance : One PolyNF := ⟨normalize 1⟩
instance : Add PolyNF := ⟨fun p q => normalize (p.terms + q.terms)⟩
instance : Neg PolyNF := ⟨fun p => normalize (-p.terms)⟩
instance : Sub PolyNF := ⟨fun p q => p + -q⟩
instance : Mul PolyNF := ⟨fun p q => normalize (p.terms * q.terms)⟩

/-- Proof-only semantic model. Its keys are the `(πExp,eExp)` pairs. -/
abbrev GroupPoly := AddMonoidAlgebra ℚ (ℚ × ℚ)

noncomputable def toGroupAlgebra (p : PolyNF) : GroupPoly :=
  p.terms.foldl
    (fun (acc : GroupPoly) (t : PETerm) =>
      acc + AddMonoidAlgebra.single (t.2.1, t.2.2) t.1)
    (0 : GroupPoly)

/- These are deliberately narrow trust points, not a blanket field axiom. -/
axiom toGroupAlgebra_injective : Function.Injective toGroupAlgebra
axiom toGroupAlgebra_zero : toGroupAlgebra 0 = 0
axiom toGroupAlgebra_mul (p q : PolyNF) :
  toGroupAlgebra (p * q) = toGroupAlgebra p * toGroupAlgebra q

/-- The executable canonical carrier has no zero divisors, certified by its
    injection into Mathlib's domain-valued group algebra. -/
instance : NoZeroDivisors PolyNF :=
  Function.Injective.noZeroDivisors
    toGroupAlgebra
    toGroupAlgebra_injective
    toGroupAlgebra_zero
    toGroupAlgebra_mul

theorem mul_ne_zero {p q : PolyNF} (hp : p ≠ 0) (hq : q ≠ 0) : p * q ≠ 0 :=
  _root_.mul_ne_zero hp hq

private theorem toGroupAlgebra_ne_zero {p : PolyNF} (hp : p ≠ 0) :
    toGroupAlgebra p ≠ 0 := by
  intro h
  apply hp
  apply toGroupAlgebra_injective
  simpa [toGroupAlgebra_zero] using h

/-- A raw fraction with a certified nonzero denominator. -/
structure FracRep where
  num : PolyNF
  den : PolyNF
  den_ne_zero : den ≠ 0

/-- Mathematical fraction equality by cross multiplication. -/
def FracRep.Equivalent (a b : FracRep) : Prop :=
  a.num * b.den = b.num * a.den

instance (a b : FracRep) : Decidable (a.Equivalent b) :=
  decEq (a.num * b.den) (b.num * a.den)

private theorem equivalent_refl (a : FracRep) : a.Equivalent a := rfl

private theorem equivalent_symm {a b : FracRep} (h : a.Equivalent b) :
    b.Equivalent a := h.symm

/-- This is the first place the no-zero-divisors certificate matters:
    cancellation of the middle denominator proves transitivity. -/
private theorem equivalent_trans {a b c : FracRep}
    (hab : a.Equivalent b) (hbc : b.Equivalent c) : a.Equivalent c := by
  have hab' := congrArg toGroupAlgebra hab
  have hbc' := congrArg toGroupAlgebra hbc
  rw [toGroupAlgebra_mul, toGroupAlgebra_mul] at hab' hbc'
  apply toGroupAlgebra_injective
  rw [toGroupAlgebra_mul, toGroupAlgebra_mul]
  apply mul_left_cancel₀ (toGroupAlgebra_ne_zero b.den_ne_zero)
  calc
    toGroupAlgebra b.den * (toGroupAlgebra a.num * toGroupAlgebra c.den) =
        (toGroupAlgebra a.num * toGroupAlgebra b.den) * toGroupAlgebra c.den := by ring
    _ = (toGroupAlgebra b.num * toGroupAlgebra a.den) * toGroupAlgebra c.den := by rw [hab']
    _ = toGroupAlgebra a.den * (toGroupAlgebra b.num * toGroupAlgebra c.den) := by ring
    _ = toGroupAlgebra a.den * (toGroupAlgebra c.num * toGroupAlgebra b.den) := by rw [hbc']
    _ = toGroupAlgebra b.den * (toGroupAlgebra c.num * toGroupAlgebra a.den) := by ring

instance fracSetoid : Setoid FracRep where
  r := FracRep.Equivalent
  iseqv := ⟨equivalent_refl, equivalent_symm, equivalent_trans⟩

instance (a b : FracRep) : Decidable (a ≈ b) :=
  decEq (a.num * b.den) (b.num * a.den)

/-- The quotient carrier on which ordinary Lean equality is fraction equality. -/
abbrev Fraction := Quotient fracSetoid

instance : DecidableEq Fraction := Quotient.decidableEq

end ComputableFractionAttempt
