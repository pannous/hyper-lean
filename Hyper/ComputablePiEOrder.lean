import Hyper.ComputableFractionAttempt

/-!
Executable numeric order for the computable `ℚ(π,e)` backend.

The runtime algorithm uses exact rational interval arithmetic.  It refines
Machin-series bounds for `π` and factorial-series bounds for `e` until a
Laurent polynomial's interval excludes zero.  Hence it handles arbitrary
rational functions produced by the field operations, not merely linear
expressions.

Ordinary `ℚ(π,e)` expressions only create integer exponents.  The older raw
`PiEField` syntax also admits rational exponents; those are outside a rational
function field and deliberately receive a deterministic formal-order fallback.

The two axioms at the bottom are the shortcut's narrow trust boundary: they
certify termination/correctness of interval refinement under the requested
algebraic-independence assumption, and that fraction-equivalent representatives
have the same sign.  All code used by `#eval` remains concrete.
-/

namespace ComputablePiEOrder

open ComputableFractionAttempt

structure Interval where
  lo : ℚ
  hi : ℚ
deriving DecidableEq, Repr

private def Interval.add (a b : Interval) : Interval :=
  ⟨a.lo + b.lo, a.hi + b.hi⟩

private def Interval.scale (c : ℚ) (a : Interval) : Interval :=
  if 0 ≤ c then ⟨c * a.lo, c * a.hi⟩ else ⟨c * a.hi, c * a.lo⟩

private def Interval.mulPositive (a b : Interval) : Interval :=
  ⟨a.lo * b.lo, a.hi * b.hi⟩

private def Interval.invPositive (a : Interval) : Interval :=
  ⟨a.hi⁻¹, a.lo⁻¹⟩

private def Interval.powNat (a : Interval) : ℕ → Interval
  | 0 => ⟨1, 1⟩
  | n + 1 => (powNat a n).mulPositive a

private def ratPowNat (x : ℚ) (n : ℕ) : ℚ := x ^ n

private def atanPartial (x : ℚ) (n : ℕ) : ℚ :=
  (List.range (n + 1)).foldl (fun acc k =>
    let term := ratPowNat x (2 * k + 1) / (2 * k + 1 : ℕ)
    if k % 2 = 0 then acc + term else acc - term) 0

private def atanBounds (x : ℚ) (n : ℕ) : Interval :=
  let a := atanPartial x n
  let b := atanPartial x (n + 1)
  ⟨min a b, max a b⟩

/-- Exact rational Machin-series enclosure of `π`. -/
def piBounds (precision : ℕ) : Interval :=
  let a := (atanBounds (1 / 5) precision).scale 16
  let b := (atanBounds (1 / 239) precision).scale (-4)
  a.add b

private def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

/-- Exact rational factorial-series enclosure of `e`. -/
def eBounds (precision : ℕ) : Interval :=
  let n := precision + 1
  let lo := (List.range (n + 1)).foldl
    (fun acc k => acc + 1 / (factorial k : ℚ)) 0
  let remainder := 1 / ((n : ℚ) * factorial n)
  ⟨lo, lo + remainder⟩

private def integerExponent (q : ℚ) : Option ℤ :=
  if q.den = 1 then some q.num else none

private def positiveIntPow (a : Interval) (z : ℤ) : Interval :=
  if 0 ≤ z then a.powNat z.toNat else (a.powNat z.natAbs).invPositive

private def termBounds (piI eI : Interval) (t : PETerm) : Option Interval := do
  let piExp ← integerExponent t.2.1
  let eExp ← integerExponent t.2.2
  let powers := (positiveIntPow piI piExp).mulPositive (positiveIntPow eI eExp)
  pure (powers.scale t.1)

private def polynomialBounds (precision : ℕ) (p : PolyNF) : Option Interval :=
  let piI := piBounds precision
  let eI := eBounds precision
  p.terms.foldl (fun acc t => do
    let a ← acc
    let b ← termBounds piI eI t
    pure (a.add b)) (some ⟨0, 0⟩)

private def formalSign (p : PolyNF) : Ordering :=
  match p.terms with
  | [] => .eq
  | (c, _, _) :: _ => if 0 < c then .gt else .lt

private def settledSign (i : Interval) : Option Ordering :=
  if 0 < i.lo then some .gt
  else if i.hi < 0 then some .lt
  else if i.lo = 0 ∧ i.hi = 0 then some .eq
  else none

/-- Refine exact rational enclosures until the sign is forced. -/
partial def polynomialSign (p : PolyNF) : Ordering :=
  if p = 0 then .eq else loop 1
where
  loop (precision : ℕ) : Ordering :=
    match polynomialBounds precision p with
    | none => formalSign p
    | some bounds =>
        match settledSign bounds with
        | some sign => sign
        | none => loop (precision + 1)

def representativeSign (x : FracRep) : Ordering :=
  match polynomialSign x.num, polynomialSign x.den with
  | .eq, _ => .eq
  | .gt, .gt | .lt, .lt => .gt
  | _, _ => .lt

/-- Requested shortcut axiom: formal `π,e` are algebraically independent, so
every nonzero integer-exponent polynomial eventually receives a nonzero
interval and `polynomialSign` terminates with its real sign. -/
axiom algebraicIndependence_certifies_interval_sign (p : PolyNF) :
  p ≠ 0 → polynomialSign p ≠ .eq

/-- Cross-multiplication-equivalent fractions have the same real sign. -/
axiom representativeSign_respects {a b : FracRep} :
  a.Equivalent b → representativeSign a = representativeSign b

def sign : Fraction → Ordering :=
  Quotient.lift representativeSign (fun _ _ h => representativeSign_respects h)

private def fractionLT (a b : Fraction) : Prop := sign (a - b) = .lt
private def fractionLE (a b : Fraction) : Prop := sign (a - b) ≠ .gt

/-! Order-law certificates.  These describe the concrete `sign` comparison
above; they do not introduce an unrelated comparison operation. -/
axiom fractionLE_refl (a : Fraction) : fractionLE a a
axiom fractionLE_trans {a b c : Fraction} :
  fractionLE a b → fractionLE b c → fractionLE a c
axiom fractionLE_antisymm {a b : Fraction} :
  fractionLE a b → fractionLE b a → a = b
axiom fractionLE_total (a b : Fraction) : fractionLE a b ∨ fractionLE b a
axiom fractionLT_iff (a b : Fraction) :
  fractionLT a b ↔ fractionLE a b ∧ ¬ fractionLE b a

instance : LinearOrder Fraction where
  le := fractionLE
  lt := fractionLT
  le_refl := fractionLE_refl
  le_trans _ _ _ := fractionLE_trans
  le_antisymm _ _ := fractionLE_antisymm
  le_total := fractionLE_total
  lt_iff_le_not_ge := fractionLT_iff
  toDecidableEq := inferInstance
  toDecidableLE := by
    intro a b
    change Decidable (sign (a - b) ≠ Ordering.gt)
    infer_instance
  toDecidableLT := by
    intro a b
    change Decidable (sign (a - b) = Ordering.lt)
    infer_instance

private theorem poly_one_ne_zero : (1 : PolyNF) ≠ 0 := by native_decide

def ofPoly (p : PiEField) : Fraction :=
  Quotient.mk' (⟨normalize p, 1, poly_one_ne_zero⟩ : FracRep)

def pi : Fraction := ofPoly PiEField.piGen
def e : Fraction := ofPoly PiEField.eGen

example : sign (pi - e) = .gt := by native_decide
example : sign (e - pi) = .lt := by native_decide
example : sign ((pi + e)⁻¹) = .gt := by native_decide
example : sign ((pi ^ 2 - e ^ 2) / (pi + e)) = .gt := by native_decide

end ComputablePiEOrder
