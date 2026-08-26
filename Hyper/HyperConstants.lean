/-
  Adjoining π and e as formal generators, alongside ε and ω.
  =============================================================

  Real algebraic numbers don't contain π or e — both are transcendental
  (Lindemann 1882, Hermite 1873), so no field extension built from roots of
  rational polynomials can reach them. But `ℚ(π)`, as an *abstract* field
  extension, is isomorphic to `ℚ(x)` — the field of rational functions in a
  fresh indeterminate — precisely because π is transcendental: there is no
  algebraic relation to quotient by. So "adjoin π as a formal symbol" isn't
  a hack standing in for the real thing; it's an exact description of what
  that field extension *is*, in exactly the same sense `Hyper/HyperList.lean`
  already adjoins ε formally (`R* = ℚ[ε, ω]/(εω = 1)`, a Laurent-polynomial
  ring in one variable, not an approximation of anything).

  This file does the same for π and e: instead of a single ε-exponent, each
  term carries three independent exponents `(εExp, πExp, eExp)`. It is a
  small, standalone, deliberately separate file — see
  `notes/hyperreal-formal-constants.md` for why it doesn't touch
  `Hyper/HyperList.lean` in place.

  ⚠️ No relation between π and e is assumed anywhere below, on purpose.
  Whether π and e are even algebraically independent (whether some nonzero
  rational polynomial in both could ever vanish) is a genuine open problem
  in number theory — nobody knows if `π + e` or `π · e` is irrational. The
  only honest default is to treat them as free, independent generators: it
  costs nothing (a proven relation could always be added later as an
  explicit rewrite), and it never risks asserting something unproven.

  ⚠️ This is a purely symbolic/algebraic ring. There is no numeric
  evaluation here — `piGen` is a formal marker, not (an approximation of)
  3.14159...; getting an actual decimal out of an expression involving it
  is a separate concern this file doesn't address.
-/
import Mathlib.Data.EReal.Basic
import Mathlib.Tactic.NormNum

notation "𝔽" => ℚ

namespace Hypers
namespace HyperConstants

/-- A term `(coefficient, εExp, πExp, eExp)`: `coefficient · ε^εExp · π^πExp · e^eExp`. -/
abbrev Term := 𝔽 × 𝔽 × 𝔽 × 𝔽

/-- Sums of monomials in `ε`, `π`, `e` — same list-of-terms representation as
    `Hyper.HyperList.HyperList`, generalized from one exponent to three. -/
abbrev HyperExt : Type := List Term

notation "R⋆" => HyperExt

instance : DecidableEq Term := inferInstance
instance : DecidableEq R⋆ := inferInstance

instance : Zero R⋆ := ⟨([] : R⋆)⟩
instance : One R⋆ := ⟨[(1, 0, 0, 0)]⟩

/-- The infinitesimal, as before: `[(1, 1, 0, 0)]` = `1 · ε¹ · π⁰ · e⁰`. -/
def epsilon : R⋆ := [(1, 1, 0, 0)]
/-- `ω = ε⁻¹`, as before. -/
def omega : R⋆ := [(1, -1, 0, 0)]
/-- π, adjoined as an independent formal generator — not a numeric constant. -/
def piGen : R⋆ := [(1, 0, 1, 0)]
/-- e, adjoined as an independent formal generator — not a numeric constant. -/
def eGen : R⋆ := [(1, 0, 0, 1)]

scoped notation "ε" => epsilon
scoped notation "ω" => omega
scoped notation "π'" => piGen -- `π` itself is taken by `Real.pi`/notation elsewhere
scoped notation "e'" => eGen

-- ═══════════════════════════════════════════════════════════════════════════
-- Canonical form: same recipe as `HyperList.lean` (sort, merge adjacent equal
-- keys, drop zero coefficients), with the sort/merge key now the whole
-- exponent triple instead of a single exponent.
-- ═══════════════════════════════════════════════════════════════════════════

/-- Merge consecutive terms with identical `(εExp, πExp, eExp)` in a sorted list. -/
def mergeAdjacent : List Term → List Term
  | [] => []
  | [x] => [x]
  | (r₁, x₁) :: (r₂, x₂) :: rest =>
      if x₁ = x₂ then mergeAdjacent ((r₁ + r₂, x₁) :: rest)
      else (r₁, x₁) :: mergeAdjacent ((r₂, x₂) :: rest)
termination_by l => l.length
decreasing_by all_goals (simp_all; try omega)

/-- Descending lexicographic order on `(εExp, πExp, eExp)` — any fixed total
    order works for canonicalization; which one is arbitrary. -/
def myle (p q : Term) : Bool := decide (q.2 ≤ p.2)

/-- Canonical form: sort, merge duplicate exponent-triples, drop zero coefficients. -/
def simplify (a : R⋆) : R⋆ :=
  (mergeAdjacent (a.mergeSort myle)) |>.filter (fun p => p.1 ≠ 0)

def normalize (x : R⋆) : R⋆ := simplify x

def merge (x y : R⋆) : R⋆ := if x = [] then y else if y = [] then x else simplify (x ++ y)

instance : HAppend R⋆ R⋆ R⋆ := ⟨merge⟩
instance : Add R⋆ := ⟨merge⟩
instance : Neg R⋆ := ⟨fun x => x.map (fun (r, e) => (-r, e))⟩
instance : Sub R⋆ := ⟨fun x y => x + -y⟩

/-- Multiplication: cartesian product of terms, multiply coefficients, **add
    exponent triples componentwise** — this is where independence actually
    lives. There is no rule anywhere that lets a π-exponent bleed into an
    ε-exponent or an e-exponent, or vice versa; the three tracks never mix. -/
instance : Mul R⋆ := ⟨fun x y =>
  normalize ((x.product y).map
    (fun ((r1, e1), (r2, e2)) => (r1 * r2, e1.1 + e2.1, e1.2.1 + e2.2.1, e1.2.2 + e2.2.2)))⟩

/-- Termwise monomial inverse — exact only for single-term `R⋆` values, same
    documented limitation as `Hyper.HyperList.HyperList`'s `Inv` instance. -/
instance : Inv R⋆ := ⟨fun x => x.map (fun (r, e) => (r⁻¹, -e.1, -e.2.1, -e.2.2))⟩
instance : HDiv R⋆ R⋆ R⋆ := ⟨fun x y => x * y⁻¹⟩

instance : Repr R⋆ := inferInstanceAs (Repr (List Term))

-- ═══════════════════════════════════════════════════════════════════════════
-- Sanity checks: the generators are nonzero, distinct, self-inverse in the
-- monomial sense — and, the actual point of this file, genuinely
-- independent: a mixed product produces new cross terms rather than
-- collapsing anything.
-- ═══════════════════════════════════════════════════════════════════════════

example : (π' : R⋆) ≠ 0 := by native_decide
example : (e' : R⋆) ≠ 0 := by native_decide
example : (π' : R⋆) ≠ e' := by native_decide
example : (ε : R⋆) ≠ π' := by native_decide
example : (ε : R⋆) ≠ e' := by native_decide

example : (π' : R⋆) * π'⁻¹ = 1 := by native_decide
example : (e' : R⋆) * e'⁻¹ = 1 := by native_decide

-- Independence, made concrete: (ε + π)² expands to three genuinely distinct
-- terms (ε², 2·ε·π, π²) — no algebraic relation ever lets the cross term
-- `ε·π` simplify away or collapse into either pure power.
example : ((ε + π') * (ε + π') : R⋆) = [(1, 2, 0, 0), (2, 1, 1, 0), (1, 0, 2, 0)] := by
  native_decide
example : (ε * ε : R⋆) ≠ (π' * π' : R⋆) := by native_decide

-- Likewise for e, and for a genuinely three-way mixed product.
example : ((π' + e') * (π' + e') : R⋆) = [(1, 0, 2, 0), (2, 0, 1, 1), (1, 0, 0, 2)] := by
  native_decide
example : (ε * π' * e' : R⋆) = [(1, 1, 1, 1)] := by native_decide

end HyperConstants
end Hypers
