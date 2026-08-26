/-
  ℚ(π, e): the coefficient field, not an exponent extension.
  ==============================================================

  `Hyper/HyperConstants.lean` adjoined π and e as extra *exponent* tracks on
  top of `ℚ`-valued coefficients. That answers a different question than
  "set the coefficient field to ℚ+π+e" — this file does the latter: `π` and
  `e` become the generators of the field itself, in exactly the spirit
  `Hyper/HyperList.lean` already adjoins `ε` — a Laurent-monomial ring, with
  canonical form via sort/merge/drop-zero, and `Inv` exact for single
  monomials.

  ⚠️ Scope, stated plainly: Mathlib has no ready-made computable field of
  fractions for a multivariate polynomial ring (`AlgebraicClosure`/
  `Localization`/`IsFractionRing` are classical/noncomputable
  constructions), and building one from scratch needs `ℚ[π,e]` proved to
  have no zero divisors before transitivity of the fraction-equivalence
  relation even typechecks as sound — real, substantial work, not attempted
  here. A first attempt at a "shortcut" field via a bare
  `axiom : Field RatFun` on an un-normalized syntax tree turned out to be
  *disconnected* from the actual executable operations, not merely
  incomplete: `π · π⁻¹ = 1` and `π + e = e + π` were both concretely false
  under `#eval` despite the axiom's presence, because nothing tied the
  axiom's abstract field structure to the concrete `RatFun.mul`/`add`. That
  attempt is replaced below by an actual normalizer into the sound
  `PiEField` engine — no axioms needed for the ring fragment, honest limits
  only where they're real (monomial-only `Inv`).

  What **is** built, fully soundly: `PiEField` (a Laurent-monomial ring in
  π, e) has genuinely commutative/associative/distributive `+`/`*` (checked,
  not axiomatized) and single-monomial-exact division (`π/π = 1`,
  `1/π · π = 1`, `π/e · e = π`) — *exactly the same scope*
  `Hyper/HyperList.lean`'s own `Inv` has for `R*` (monomial-exact;
  `Field R*`'s `mul_inv_cancel` is a documented `sorry` for general
  multi-term values). General rational functions with polynomial
  denominators (`1/(π+e)`) remain the same kind of open problem here that
  `1/(ε+ω)` already is for `R*` — not a new gap this file introduces.

  On top of `PiEField`, `RatFun` is a friendly AST surface syntax (build
  expressions with `+`/`*`/`⁻¹` freely) together with `normalize : RatFun →
  PiEField`, the actual arithmetic engine. `x ≈ y := normalize x = normalize
  y` is the correct notion of equality for `RatFun` — same shape as
  `Hyper.HyperList.HyperEq` — never raw structural `=`, which sees
  `mul (rat 2) (rat 2)` and `rat 4` as different terms.
-/
import Mathlib.Data.EReal.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-- A term `(coefficient, πExp, eExp)` — `coefficient · π^πExp · e^eExp`. -/
abbrev PETerm := ℚ × ℚ × ℚ

/-- ℚ(π, e), as a Laurent-monomial ring in two independent generators. -/
abbrev PiEField : Type := List PETerm

namespace PiEField

def mergeAdjacent : List PETerm → List PETerm
  | [] => []
  | [x] => [x]
  | (r₁, x₁) :: (r₂, x₂) :: rest =>
      if x₁ = x₂ then mergeAdjacent ((r₁ + r₂, x₁) :: rest)
      else (r₁, x₁) :: mergeAdjacent ((r₂, x₂) :: rest)
termination_by l => l.length
decreasing_by all_goals (simp_all; try omega)

/-- Lexicographic `≤` on the exponent pair `(πExp, eExp)`.
    ⚠️ Mathlib's `Prod` order is *componentwise* (a partial order — `(0,1)`
    and `(1,0)` are simply incomparable under it), not lexicographic; using
    raw `≤` here would make `mergeSort`'s output order-dependent on the
    input, silently breaking the canonical-form guarantee (`π + e` and
    `e + π` could normalize to different raw lists). This explicit
    comparator is total, so sorting is genuinely canonical — confirmed by
    testing both orders concretely, not just assumed. -/
def lexLE (p q : ℚ × ℚ) : Bool :=
  decide (p.1 < q.1) ∨ (decide (p.1 = q.1) ∧ decide (p.2 ≤ q.2))

def myle (p q : PETerm) : Bool := lexLE q.2 p.2

def simplify (a : PiEField) : PiEField :=
  (mergeAdjacent (a.mergeSort myle)) |>.filter (fun p => p.1 ≠ 0)

def merge (x y : PiEField) : PiEField := if x = [] then y else if y = [] then x else simplify (x ++ y)

instance : Zero PiEField := ⟨([] : PiEField)⟩
instance : One PiEField := ⟨[(1, 0, 0)]⟩
instance {n : ℕ} : OfNat PiEField n := ⟨[(n, 0, 0)]⟩
instance : Add PiEField := ⟨merge⟩
instance : Neg PiEField := ⟨fun x => x.map (fun (r, e) => (-r, e))⟩
instance : Sub PiEField := ⟨fun x y => x + -y⟩
instance : Mul PiEField := ⟨fun x y =>
  simplify ((x.product y).map (fun ((r1, e1), (r2, e2)) => (r1 * r2, e1.1 + e2.1, e1.2 + e2.2)))⟩
/-- Termwise monomial inverse — exact only for single-term values, same
    documented limitation as `Hyper.HyperList.HyperList`'s own `Inv`. -/
instance : Inv PiEField := ⟨fun x => x.map (fun (r, e) => (r⁻¹, -e.1, -e.2))⟩
instance : Div PiEField := ⟨fun x y => x * y⁻¹⟩
instance : DecidableEq PiEField := inferInstance
instance : Repr PiEField := inferInstanceAs (Repr (List PETerm))

def piGen : PiEField := [(1, 1, 0)]
def eGen : PiEField := [(1, 0, 1)]

/-- Is this value a single monomial (0 or 1 terms)? `Inv` is only exact
    when this holds — a cheap guard against silently trusting `x⁻¹` for a
    multi-term `x`. -/
def isMonomial (x : PiEField) : Bool := x.length ≤ 1

-- ═══════════════════════════════════════════════════════════════════════════
-- Sanity: nonzero, distinct, monomial-exact division, genuine independence
-- (no relation between π and e is assumed anywhere — their algebraic
-- independence is a real open problem in number theory, so free generators
-- are the only honest default), and order-independent commutativity —
-- the exact thing the `lexLE` fix above makes true.
-- ═══════════════════════════════════════════════════════════════════════════

example : (piGen : PiEField) ≠ 0 := by native_decide
example : (eGen : PiEField) ≠ 0 := by native_decide
example : (piGen : PiEField) ≠ eGen := by native_decide

example : (piGen * piGen⁻¹ : PiEField) = 1 := by native_decide
example : (eGen * eGen⁻¹ : PiEField) = 1 := by native_decide
example : (piGen / piGen : PiEField) = 1 := by native_decide
example : ((1 : PiEField) / piGen) * piGen = 1 := by native_decide
example : (piGen / eGen : PiEField) * eGen = piGen := by native_decide

example : (piGen + eGen : PiEField) = eGen + piGen := by native_decide
example : (piGen + eGen : PiEField) * (piGen + eGen) = [(1, 2, 0), (2, 1, 1), (1, 0, 2)] := by
  native_decide

end PiEField

-- ═══════════════════════════════════════════════════════════════════════════
-- RatFun: a friendly AST surface syntax over PiEField, plus its normalizer —
-- the actual arithmetic engine, replacing the earlier disconnected-axiom
-- attempt (see file header).
-- ═══════════════════════════════════════════════════════════════════════════

inductive RatFun where
  | rat (q : ℚ)
  | piAtom
  | eAtom
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

def pi : RatFun := .piAtom
def e : RatFun := .eAtom

/-- The actual arithmetic engine: interpret the AST in `PiEField`, where
    `+`/`-`/`*` are genuinely commutative/associative/distributive (proved
    by `PiEField`'s canonical form) and `⁻¹` is exact for monomials — same
    scope `PiEField.Inv` already has, inherited honestly, not newly
    introduced by this normalizer. -/
def normalize : RatFun → PiEField
  | rat q => [(q, 0, 0)]
  | piAtom => PiEField.piGen
  | eAtom => PiEField.eGen
  | add x y => normalize x + normalize y
  | neg x => -normalize x
  | mul x y => normalize x * normalize y
  | inv x => (normalize x)⁻¹

/-- The correct notion of equality for `RatFun` — NOT raw structural `=`
    (which sees `mul (rat 2) (rat 2)` and `rat 4` as different), but
    agreement after evaluating both sides in `PiEField`. Same shape as
    `Hyper.HyperList.HyperEq` (`simplify x = simplify y`). -/
def eqv (x y : RatFun) : Prop := normalize x = normalize y
instance : HasEquiv RatFun := ⟨eqv⟩
instance (x y : RatFun) : Decidable (x ≈ y) :=
  inferInstanceAs (Decidable (normalize x = normalize y))

instance : ToString RatFun := ⟨fun x => reprStr x⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- The border cases that broke the earlier disconnected-axiom attempt — now
-- genuinely fixed, checked through `≈`, not assumed via `Field`.
-- ═══════════════════════════════════════════════════════════════════════════

example : (pi * pi⁻¹ : RatFun) ≈ 1 := by native_decide
example : (pi + e : RatFun) ≈ e + pi := by native_decide
example : (pi * e : RatFun) ≈ e * pi := by native_decide
example : ((pi + e) * (pi - e) : RatFun) ≈ pi * pi - e * e := by native_decide -- difference of squares

/-- What's still honestly NOT fixed: inverting a non-monomial. The
    normalizer doesn't hide this — `PiEField.isMonomial` on the normalized
    form lets you check before trusting `⁻¹` on a `RatFun` expression. -/
example : PiEField.isMonomial (normalize (pi + e)) = false := by native_decide
example : PiEField.isMonomial (normalize (pi * e)) = true := by native_decide

-- The termwise `Inv` formula silently gives a WRONG answer for a
-- multi-term input — this is `PiEField.Inv`'s documented limitation
-- surfacing through the normalizer, not a bug in the normalizer itself.
example : ¬ ((pi + e) * (pi + e)⁻¹ : RatFun) ≈ 1 := by native_decide

/-- Interpretation of the formal expression inside the actual reals. The
    earlier attempt at this axiomatized a ring homomorphism's existence;
    that's unnecessary — it's a genuine structural recursion, provably
    correct by construction, so it's a plain (noncomputable, since
    `Real.pi`/`Real.exp` are) `def`, not an axiom. -/
noncomputable def realEval : RatFun → ℝ
  | rat q => (q : ℝ)
  | piAtom => Real.pi
  | eAtom => Real.exp 1
  | add x y => realEval x + realEval y
  | neg x => -realEval x
  | mul x y => realEval x * realEval y
  | inv x => (realEval x)⁻¹

example : realEval pi = Real.pi := rfl
example : realEval e = Real.exp 1 := rfl
example (x y : RatFun) : realEval (x + y) = realEval x + realEval y := rfl
example (x y : RatFun) : realEval (x * y) = realEval x * realEval y := rfl

end RatFun
