import Mathlib
import Hyper.HyperGeneric

/-!
The optional coefficient backend `ℚ(X,Y)`.

This is the exact rational-function field supplied by Mathlib.  The two
formal indeterminates are exported as `pi` and `e`; a separate axiom records
the intended (currently unproved) interpretation by the real numbers π and e.

The backend is intentionally kept independent of `HyperList`, so clients can
switch coefficient fields without changing the old rational implementation.
Mathlib's `FractionRing` is exact but noncomputable (its quotient equality is
classical); this is why it is exposed as an optional backend rather than
silently replacing the executable rational model.
-/

abbrev PEVar := Fin 2
abbrev PEPoly := MvPolynomial PEVar ℚ

namespace PiEField

noncomputable section

abbrev Field := FractionRing PEPoly

/- Fraction fields are exact but their equality is not executable in Mathlib;
   this classical instance keeps the backend usable by generic algebraic code. -/
scoped instance : DecidableEq Field := Classical.decEq Field

def ofRat (q : ℚ) : Field := algebraMap PEPoly Field (MvPolynomial.C q)

def pi : Field := algebraMap PEPoly Field (MvPolynomial.X 0)

def e : Field := algebraMap PEPoly Field (MvPolynomial.X 1)

instance : Repr Field := ⟨fun _ _ => Std.Format.text "ℚ(π,e)"⟩
instance : ToString Field := ⟨fun _ => "ℚ(π,e)"⟩

end

end PiEField

namespace PiEField

abbrev Hyper := GHyper Field

noncomputable def piTerm : Hyper := [(pi, 0)]
noncomputable def eTerm : Hyper := [(e, 0)]

end PiEField

/- The concrete real interpretation used by the project axiom. -/
noncomputable def piEReal : PEVar → ℝ
  | ⟨0, _⟩ => Real.pi
  | ⟨1, _⟩ => Real.exp 1

axiom pi_e_algebraicIndependent : AlgebraicIndependent ℚ piEReal
