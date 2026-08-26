/-
  A hyperreal construction generic in its coefficient field.
  ==============================================================

  `Hyper/HyperQuadField.lean` got a `Quad d`-coefficient hyperreal type by
  copy-adapting `HyperList.lean`'s term/`simplify`/`merge`/`Mul` machinery by
  hand into a second file. That's not the right shape: the coefficient
  field should be **extensible from outside**, the same way `ε`/`ω` are
  just generators anyone can build on — not something that needs the whole
  construction re-derived per field.

  This file makes that literal: `GHyper F` is parametrized over an arbitrary
  coefficient type `F`, constrained only by the six instances the
  construction actually uses (`Zero`, `One`, `Add`, `Neg`, `Mul`,
  `DecidableEq`). Plug in `F := ℚ` and you get exactly `HyperList.lean`'s
  behaviour back; plug in `F := Quad d` (`Hyper/QuadField.lean`) and you get
  `HyperQuadField.lean`'s irrational-coefficient hyperreals — with **zero
  code duplicated between the two**, checked below by re-proving the same
  facts through the one generic definition.

  Note the sort/merge key (`myle`) only ever looks at the *exponent*, which
  stays `ℚ` regardless of `F` — so `F` needs no order at all for this much
  of the construction (`+`, `*`, the generators) to work. A generic `<`/`≤`
  on `GHyper F` itself (comparing hyperreal *values*, `HyperList.lean`'s
  `leadSign`) would need `F` to supply an order too; not attempted here,
  same scope boundary as `HyperQuadField.lean`.
-/
import Hyper.QuadField

/-- A term `(coefficient, εExp)`, generic in the coefficient type `F`. -/
abbrev GTerm (F : Type) := F × ℚ

/-- Hyperreal numbers with coefficients in an arbitrary `F` — supply the six
    instances below (from *outside* this file, for any `F` you like) and
    the whole construction — `simplify`, `+`, `*`, `ε`, `ω` — comes for free. -/
abbrev GHyper (F : Type) : Type := List (GTerm F)

namespace GHyper

variable {F : Type} [Zero F] [One F] [Add F] [Neg F] [Mul F] [DecidableEq F]

def mergeAdjacent : List (GTerm F) → List (GTerm F)
  | [] => []
  | [x] => [x]
  | (r₁, e₁) :: (r₂, e₂) :: rest =>
      if e₁ = e₂ then mergeAdjacent ((r₁ + r₂, e₁) :: rest)
      else (r₁, e₁) :: mergeAdjacent ((r₂, e₂) :: rest)
termination_by l => l.length
decreasing_by all_goals (simp_all; try omega)

/-- Descending order by exponent — same convention as `HyperList.lean`'s
    `myle`, and note it only ever inspects `ℚ`, never `F`. -/
def myle (p q : GTerm F) : Bool := decide (q.2 ≤ p.2)

def simplify (a : GHyper F) : GHyper F :=
  (mergeAdjacent (a.mergeSort myle)) |>.filter (fun p => p.1 ≠ 0)

def merge (x y : GHyper F) : GHyper F :=
  if x = [] then y else if y = [] then x else simplify (x ++ y)

instance : Zero (GHyper F) := ⟨([] : GHyper F)⟩
instance : One (GHyper F) := ⟨[(1, 0)]⟩
instance : Add (GHyper F) := ⟨merge⟩
instance : Neg (GHyper F) := ⟨fun x => x.map (fun (r, e) => (-r, e))⟩
instance : Sub (GHyper F) := ⟨fun x y => x + -y⟩
instance : Mul (GHyper F) := ⟨fun x y =>
  simplify ((x.product y).map (fun ((r1, e1), (r2, e2)) => (r1 * r2, e1 + e2)))⟩

def epsilon : GHyper F := [(1, -1)]
def omega : GHyper F := [(1, 1)]

end GHyper

-- ═══════════════════════════════════════════════════════════════════════════
-- Instantiation 1: `F := ℚ` — reproduces `HyperList.lean`'s behaviour,
-- through the generic code, not a reimplementation of it.
-- ═══════════════════════════════════════════════════════════════════════════

example : (GHyper.epsilon (F := ℚ)) * GHyper.omega = 1 := by native_decide
example : (GHyper.epsilon (F := ℚ)) + GHyper.epsilon = ([(2, -1)] : GHyper ℚ) := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- Instantiation 2: `F := Quad d` — the *same* generic definitions above,
-- supplied nothing but `Quad d`'s existing `Zero`/`One`/`Add`/`Neg`/`Mul`/
-- `DecidableEq` instances from `Hyper/QuadField.lean`, immediately produce
-- irrational-coefficient hyperreals. This is the actual point: no second
-- copy of `simplify`/`merge`/`Mul` was written for this case.
-- ═══════════════════════════════════════════════════════════════════════════

/-- `√d`, embedded as a `GHyper (Quad d)` coefficient. -/
def sqrtCoeff {d : ℤ} : GHyper (Quad d) := [(Quad.sqrtGen, 0)]

example : (GHyper.epsilon (F := Quad 2)) * GHyper.omega = 1 := by native_decide
example : (sqrtCoeff * sqrtCoeff : GHyper (Quad 2)) = ([(2, 0)] : GHyper (Quad 2)) := by
  native_decide
example : (sqrtCoeff * GHyper.epsilon * GHyper.omega : GHyper (Quad 2)) = sqrtCoeff := by
  native_decide
