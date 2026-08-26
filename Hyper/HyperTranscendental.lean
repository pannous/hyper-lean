import Hyper.HyperList

/-!
Exact-rational Taylor-series `exp`/`sin`/`cos` on the concrete `R*` model.

This resurrects the *intent* of an abandoned implementation, not its code: an
earlier `Hyper/HyperReal.lean` (see commit `a044187`, "add missing") defined a
`Float`-based `Hyper` with `exp`/`sin`/`cos` via truncated Taylor series and
`log`/`sqrt`/`integrate` left as bare `sorry`s. That module was later replaced
by the current `abbrev HyperReal := HyperList` (see `Hyper/HyperReal.lean`),
so reviving it verbatim would reintroduce a second, parallel `Hyper` type
alongside `R*` — exactly the duplication the project moved away from.

The genuinely reusable idea — sum `xⁿ/n!` termwise — works just as well, and
strictly better, against `R*` directly: `R*`'s coefficients are `ℚ`
(`𝔽 := ℚ`), so every partial sum below is computed *exactly*, with no `Float`
rounding at all, unlike the old code (or `hyper.jl`'s `ComplexF64`).

⚠️ Deliberately not using `^`/`HPow` here (`hpow` below is plain repeated
multiplication): `Hyper/HyperList.lean`'s `Field R*` instance has a documented
`mul_inv_cancel := sorry`, and `^` resolves through it — fine inside a
`native_decide` proof, but it makes `#eval` abort with a sorry-axiom error
(see `Hyper/probes/HyperExamples.lean`'s header notes). Avoiding `^` keeps
every definition here plainly `#eval`-able, matching the old file's own
`#eval`-driven examples.
-/

open Hypers

namespace Hypers.HyperLists

/-- `x ^ n` by repeated multiplication, independent of the `Field R*`
    instance's `^` (see the file header for why that matters). -/
def hpow (x : R*) : ℕ → R*
  | 0 => 1
  | (n + 1) => x * hpow x n

/-- `n!` as a rational, for exact Taylor-series coefficients — the Lean-side
    counterpart of `check_factorial.lean`'s `HyperReals.factorial`. -/
def factQ : ℕ → 𝔽
  | 0 => 1
  | (n + 1) => ((n : 𝔽) + 1) * factQ n

/-- `exp(x) = ∑_{n=0}^{terms} xⁿ/n!`, truncated at `terms` (default 10, as in
    `hyper.jl`'s `TAYLOR_TERMS`), computed exactly over `ℚ`. -/
def hexp (x : R*) (terms : ℕ := 10) : R* :=
  (List.range (terms + 1)).foldl (fun acc n => acc + (1 / factQ n) • hpow x n) 0

/-- `sin(x) = ∑_{n=0}^{terms-1} (-1)ⁿ x^{2n+1}/(2n+1)!`, truncated. -/
def hsin (x : R*) (terms : ℕ := 6) : R* :=
  (List.range terms).foldl
    (fun acc n =>
      let s : 𝔽 := if n % 2 = 0 then 1 else -1
      acc + (s / factQ (2 * n + 1)) • hpow x (2 * n + 1)) 0

/-- `cos(x) = ∑_{n=0}^{terms-1} (-1)ⁿ x^{2n}/(2n)!`, truncated. -/
def hcos (x : R*) (terms : ℕ := 6) : R* :=
  (List.range terms).foldl
    (fun acc n =>
      let s : 𝔽 := if n % 2 = 0 then 1 else -1
      acc + (s / factQ (2 * n)) • hpow x (2 * n)) 0

-- ═══════════════════════════════════════════════════════════════════════════
-- Sanity: values at 0 (all series collapse to their constant term).
-- ═══════════════════════════════════════════════════════════════════════════

example : hexp (0 : R*) = 1 := by native_decide
example : hsin (0 : R*) = 0 := by native_decide
example : hcos (0 : R*) = 1 := by native_decide

-- exp(1), truncated at 10 terms, matches ⌊e⌋ = 2 as its standard part —
-- `9864101/3628800 ≈ 2.71828`, i.e. genuinely converging to Euler's number,
-- not just a placeholder value.
example : st (hexp (1 : R*) 10) = 9864101 / 3628800 := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- Hyperreal-specific: `hyper.jl`'s `@assert sin(ϵ) ~ 0` (an approximate,
-- floating-point check) becomes an *exact* statement here — `sin(ε) - ε` is
-- infinitesimal relative to `ε` itself (order ≤ -3, from the `-ε³/6 + …`
-- tail), matching the Readme's "derivative of sin at 0 is 1" intuition
-- algebraically rather than by floating-point approximation.
-- ═══════════════════════════════════════════════════════════════════════════

example : isInfinitesimal (hsin (ε : R*) - ε) = true := by native_decide
example : isInfinitesimal (hcos (ε : R*) - 1) = true := by native_decide

end Hypers.HyperLists
