import Mathlib
import Hyper.HyperGeneric

/-!
Executable shortcut backend for the formal field `ℚ(X,Y)`.

`RatFun` stores expressions directly, so construction, equality, and the basic
operations are VM-computable. The field laws are supplied by the axiom
`ratFunField`; this is the deliberate trust boundary for the shortcut
implementation. A verified normalizer can replace these constructors later
without changing users of the type.
-/

inductive RatFun where
  | rat (q : ℚ)
  | pi
  | e
  | add (x y : RatFun)
  | neg (x : RatFun)
  | mul (x y : RatFun)
  | inv (x : RatFun)
deriving DecidableEq, Repr

namespace RatFun

instance : Zero RatFun := ⟨rat 0⟩
instance : One RatFun := ⟨rat 1⟩
instance : Add RatFun := ⟨add⟩
instance : Neg RatFun := ⟨neg⟩
instance : Sub RatFun := ⟨fun x y => x + -y⟩
instance : Mul RatFun := ⟨mul⟩
instance : Inv RatFun := ⟨inv⟩
instance : Div RatFun := ⟨fun x y => x * y⁻¹⟩
instance : NatCast RatFun := ⟨fun n => rat n⟩
instance : IntCast RatFun := ⟨fun n => rat n⟩

/- The formal field theory is assumed, as requested. -/
axiom ratFunField : Field RatFun
noncomputable instance : Field RatFun := ratFunField

def piGen : RatFun := .pi
def eGen : RatFun := .e
def ofRat (q : ℚ) : RatFun := .rat q

instance : ToString RatFun := ⟨fun x => reprStr x⟩

abbrev Hyper := GHyper RatFun
def piTerm : Hyper := [(piGen, 0)]
def eTerm : Hyper := [(eGen, 0)]

end RatFun

noncomputable def piEReal : Fin 2 → ℝ
  | ⟨0, _⟩ => Real.pi
  | ⟨1, _⟩ => Real.exp 1

axiom pi_e_algebraicIndependent : AlgebraicIndependent ℚ piEReal
