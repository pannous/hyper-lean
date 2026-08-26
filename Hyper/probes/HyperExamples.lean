import Hyper.HyperList

/-!
Worked examples on the concrete `R*` model (`Hyper/HyperList.lean`), in two parts:

1. Direct ports of `@assert` lines from the canonical Julia reference
   `~/dev/script/julia/hyper.jl` (the actively-maintained copy — see
   `hyper_tests.jl` next to the project-local `hyper.jl` for the full Julia
   originals), restricted to what `R*` already supports: finite algebra on
   `ε`/`ω`, order, `abs`/`sign`, the `isFinite`/`isInfinite`/`isInfinitesimal`
   predicates, `near`/`HyperMonad`, and integer powers.
2. Border cases beyond what Julia happens to assert: empty-list/zero edge
   cases, multi-term predicates, mixed-sign `abs`/`sign`, `lead`/`least` on
   multi-term values, `hderiv`/`hint` as mutual inverses, and monad membership
   between two distinct nonzero infinitesimals.

⚠️ NOT covered here — genuinely missing on the Lean side, not just untried:
`sqrt`/`exp`/`log`/`sin`/`cos` (Julia's Taylor-series implementations, which
would need a from-scratch power-series `exp`/`log` in Lean), the `∑`/`∫`
Riemann-sum operators over functions, `taylor_series`, and `Closure`-level `≈`
(function equality sampled at a few points). `Hyper/probes/EvalsDerivatives.lean`
already covers the function-level `∂` (step/spike/Dirac-δ) independently.

Other loose root-level files (`test.lean`, `test_hyper.lean`, `test_all.lean`,
`example_working.lean`, `validate*.lean`, `check_factorial.lean`) were checked
as a possible source of more examples but all `import Hyper.Hyper` — a struct
API (`⟨3.5, 2.0, 1.5, false⟩`, `factorial`, `epsilon_times_epsilon_is_ZERO`)
that no longer exists post-reorg (`lake env lean` on any of them fails with
"object file ... Hyper/Hyper.olean does not exist"); nothing there survives
against the current `R*` model.
-/

open Hypers

namespace Hypers.HyperLists.Probes.HyperExamples

-- ═══════════════════════════════════════════════════════════════════════════
-- @assert 1/ε == ω; @assert 1/ω == ε; @assert ε*ω == 𝟙
-- @assert 1/ε == ε^-1; @assert 1/ω == ω^-1; @assert ε^0==1; @assert ω^0==1
-- ═══════════════════════════════════════════════════════════════════════════

example : (1 / ε : R*) = ω := by native_decide
example : (1 / ω : R*) = ε := by native_decide
example : (ε * ω : R*) = 1 := by native_decide
example : (1 / ε : R*) = ε⁻¹ := by native_decide
example : (1 / ω : R*) = ω⁻¹ := by native_decide
example : (ε : R*) ^ (0 : ℕ) = 1 := by native_decide
example : (ω : R*) ^ (0 : ℕ) = 1 := by native_decide

-- @assert 𝟙+𝟙-𝟙 == 𝟙; @assert 1+ε == ε+1; @assert 1+ω == ω+1
-- @assert ε*ε == 1/(ω*ω)

example : (1 : R*) + 1 - 1 = 1 := by native_decide
example : (1 : R*) + ε = ε + 1 := by native_decide
example : (1 : R*) + ω = ω + 1 := by native_decide
example : (ε : R*) * ε = 1 / (ω * ω) := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- @assert isinfinite(ω); @assert isinfinitesimal(ε); @assert isfinite(ε)
-- @assert isfinite(0); @assert isfinite(1); @assert !isinfinite(0)
-- @assert !isinfinite(ε); @assert !isfinite(ω)
-- ═══════════════════════════════════════════════════════════════════════════

example : isInfinite (ω : R*) = true := by native_decide
example : isInfinitesimal (ε : R*) = true := by native_decide
example : isFinite (ε : R*) = true := by native_decide
example : isFinite (0 : R*) = true := by native_decide
example : isFinite (1 : R*) = true := by native_decide
example : isInfinite (0 : R*) = false := by native_decide
example : isInfinite (ε : R*) = false := by native_decide
example : isFinite (ω : R*) = false := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- @assert 0 ∈ Monad(0); @assert ε ∈ Monad(0); @assert 0 ∈ Monad(ε)
-- @assert ε ∈ Monad(ε); @assert !(0.1 ∈ Monad(0)); @assert ε ∉ Monad(1)
-- ═══════════════════════════════════════════════════════════════════════════

example : inMonad 0 ⟨(0 : R*)⟩ = true := by native_decide
example : inMonad ε ⟨(0 : R*)⟩ = true := by native_decide
example : inMonad 0 ⟨(ε : R*)⟩ = true := by native_decide
example : inMonad ε ⟨(ε : R*)⟩ = true := by native_decide
example : inMonad (embedQ (1 / 10)) ⟨(0 : R*)⟩ = false := by native_decide
example : inMonad ε ⟨(1 : R*)⟩ = false := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- @assert 0<ε; @assert ε<ω; @assert 1<ω; @assert ε<1
-- @assert 0>-ε; @assert ε>-ω; @assert 1>-ω; @assert ε>-1
-- ═══════════════════════════════════════════════════════════════════════════

example : (0 : R*) < ε := by native_decide
example : (ε : R*) < ω := by native_decide
example : (1 : R*) < ω := by native_decide
example : (ε : R*) < 1 := by native_decide
example : (0 : R*) > -ε := by native_decide
example : (ε : R*) > -ω := by native_decide
example : (1 : R*) > -ω := by native_decide
example : (ε : R*) > -1 := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- @assert sign(1) == 1; @assert sign(-1) == -1; @assert sign(0) == 0
-- @assert sign(ϵ) == 1; @assert sign(-ϵ) == -1
-- @assert sign(ω) == 1; @assert sign(-ω) == -1
-- ═══════════════════════════════════════════════════════════════════════════

example : sign (1 : R*) = 1 := by native_decide
example : sign (-1 : R*) = -1 := by native_decide
example : sign (0 : R*) = 0 := by native_decide
example : sign (ε : R*) = 1 := by native_decide
example : sign (-ε : R*) = -1 := by native_decide
example : sign (ω : R*) = 1 := by native_decide
example : sign (-ω : R*) = -1 := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- @assert abs(2) == 2; @assert abs(1) == 1; @assert abs(1-ϵ) == 1-ϵ
-- @assert abs(ϵ) == ϵ; @assert abs(0) == 0; @assert abs(-ϵ) == ϵ
-- @assert abs(-1) == 1; @assert abs(-2) == 2
-- @assert abs(-1-ϵ) == 1+ϵ  # flip ALL signs, not just the leading term!
-- @assert abs(-1+ϵ) == 1-ϵ
-- ═══════════════════════════════════════════════════════════════════════════

example : abs (2 : R*) = 2 := by native_decide
example : abs (1 : R*) = 1 := by native_decide
example : abs (1 - ε : R*) = 1 - ε := by native_decide
example : abs (ε : R*) = ε := by native_decide
example : abs (0 : R*) = 0 := by native_decide
example : abs (-ε : R*) = ε := by native_decide
example : abs (-1 : R*) = 1 := by native_decide
example : abs (-2 : R*) = 2 := by native_decide
example : abs (-1 - ε : R*) = 1 + ε := by native_decide
example : abs (-1 + ε : R*) = 1 - ε := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- x = ω + 3.0 - 4.0*ω + 2.0*ε*ε + 1 - ε^2  (top of hyper.jl, both copies)
-- ═══════════════════════════════════════════════════════════════════════════

example : (ω + 3 - 4 * ω + 2 * (ε * ε) + 1 - ε * ε : R*) = -3 * ω + 4 + ε * ε := by
  native_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- Border cases: zero / the empty term list.
-- ═══════════════════════════════════════════════════════════════════════════

example : (0 : R*) * ε = 0 := by native_decide
example : (ε : R*) * 0 = 0 := by native_decide
example : (0 : R*) * ω = 0 := by native_decide
example : (0 : R*) - 0 = 0 := by native_decide
example : -(0 : R*) = 0 := by native_decide
example : isReal (0 : R*) = true := by native_decide
-- Vacuously true: `isInfinitesimal` is "every term has negative order", and
-- 0's term list is empty — 0 is not a *nonzero* infinitesimal, but it does
-- satisfy the same universally-quantified formula every genuine infinitesimal
-- does, for the same reason `∀ x ∈ (∅ : List α), p x` is always `true`.
example : isInfinitesimal (0 : R*) = true := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- Border cases: cancellation and double negation.
-- ═══════════════════════════════════════════════════════════════════════════

example : (ε : R*) - ε = 0 := by native_decide
example : (ω : R*) - ω = 0 := by native_decide
example : (ε + ω : R*) - ε - ω = 0 := by native_decide
example : (ε : R*) + (-ε) = 0 := by native_decide
example : -(-(ε : R*)) = ε := by native_decide
example : -(-(ε + ω : R*)) = ε + ω := by native_decide
example : -(ε + ω : R*) = -ε - ω := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- Border cases: predicates on genuinely multi-term values, not just single
-- monomials — a mix of orders decides `isFinite`/`isInfinite` by presence of
-- *any* term above/below order 0, not by the leading term alone.
-- ═══════════════════════════════════════════════════════════════════════════

example : isFinite (ε + 1 : R*) = true := by native_decide
example : isInfinite (ε + ω : R*) = true := by native_decide
example : isFinite (ε + ω : R*) = false := by native_decide
example : isInfinitesimal (ε + ε * ε : R*) = true := by native_decide
example : isInfinitesimal (ε + 1 : R*) = false := by native_decide
-- The product of two non-real hyperreals can itself be real.
example : isReal (ε * ω : R*) = true := by native_decide
example : isReal (ε + ω : R*) = false := by native_decide
example : isReal (5 : R*) = true := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- Border cases: `abs`/`sign` on multi-term values whose *leading* term's sign
-- disagrees with the overall shape — `abs` flips every coefficient's sign,
-- not just the dominant one (see `abs(-1-ϵ) == 1+ϵ` above), and `sign` reads
-- off the leading term only.
-- ═══════════════════════════════════════════════════════════════════════════

example : abs (ω - 1 : R*) = ω - 1 := by native_decide
example : abs (1 - ω : R*) = ω - 1 := by native_decide
example : sign (ε - ω : R*) = -1 := by native_decide
example : sign (ω - ε : R*) = 1 := by native_decide
-- abs(x) * sign(x) = x holds by construction: `abs`/`sign` are both driven by
-- the same leading-term sign check, so they always recompose to the original.
example : abs (ε - ω : R*) * sign (ε - ω : R*) = ε - ω := by native_decide
example : abs (ω - ε : R*) * sign (ω - ε : R*) = ω - ε := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- Border cases: `lead`/`least` on the empty list, a single term, and a
-- genuine multi-term spread across three distinct orders.
-- ═══════════════════════════════════════════════════════════════════════════

example : lead (0 : R*) = 0 := by native_decide
example : least (0 : R*) = 0 := by native_decide
example : lead (ε : R*) = ε := by native_decide
example : least (ε : R*) = ε := by native_decide
example : lead (ε + 1 + ω : R*) = ω := by native_decide
example : least (ε + 1 + ω : R*) = ε := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- Border case: `hderiv`/`hint` are mutual inverses (they shift every term's
-- exponent by ∓1 and nothing else touches the coefficients).
-- ═══════════════════════════════════════════════════════════════════════════

example : hderiv (hint (ε + ω : R*)) = ε + ω := by native_decide
example : hint (hderiv (ε + ω + 1 : R*)) = ε + ω + 1 := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- Border cases: `HyperMonad` membership between two distinct *nonzero*
-- infinitesimals — every infinitesimal shares the same monad (the halo of 0),
-- so `ε` and `ε²` are near each other despite being unequal and of different
-- order.
-- ═══════════════════════════════════════════════════════════════════════════

example : inMonad (ε * ε) ⟨(ε : R*)⟩ = true := by native_decide
example : inMonad ω ⟨(ε : R*)⟩ = false := by native_decide
example : inMonad (1 + ε : R*) ⟨(1 : R*)⟩ = true := by native_decide
example : inMonad (1 + ε : R*) ⟨(0 : R*)⟩ = false := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- Border cases: the full order chain around 0, including negated higher- and
-- lower-order terms (`-ω²` is more negative than `-ω`, `-ε` is less negative
-- than `-ε²` since ε² is closer to 0 than ε is).
-- ═══════════════════════════════════════════════════════════════════════════

example : (ε * ε : R*) < ε := by native_decide
example : (ε : R*) < 1 := by native_decide
example : (1 : R*) < ω := by native_decide
example : (ω : R*) < ω * ω := by native_decide
example : -(ω * ω : R*) < -ω := by native_decide
example : -(ω : R*) < -1 := by native_decide
example : (-1 : R*) < -ε := by native_decide
example : -(ε : R*) < -(ε * ε) := by native_decide
example : -(ε * ε : R*) < 0 := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- Border cases: `embedQ` on 0 and negatives, and rational round-tripping.
-- ═══════════════════════════════════════════════════════════════════════════

example : embedQ (0 : ℚ) = (0 : R*) := by native_decide
example : embedQ ((1 : ℚ) / 3) * embedQ 3 = (1 : R*) := by native_decide
example : isReal (embedQ (-5 : ℚ)) = true := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- Higher-order gauging, via both repeated multiplication and `^`.
-- ═══════════════════════════════════════════════════════════════════════════

example : (ε * ε * ε : R*) * (ω * ω * ω) = 1 := by native_decide
example : (ε : R*) ^ (3 : ℕ) * ω ^ (3 : ℕ) = 1 := by native_decide

end Hypers.HyperLists.Probes.HyperExamples
