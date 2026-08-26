import Hyper.HyperList

/-!
Direct ports of `@assert` lines from the canonical Julia reference
`~/dev/script/julia/hyper.jl` (the actively-maintained copy; the project-local
`hyper.jl` is a trimmed-down snapshot of it), restricted to what the concrete
`R*` model in `Hyper/HyperList.lean` already supports: finite algebra on
`ε`/`ω`, order, `abs`/`sign`, the `isFinite`/`isInfinite`/`isInfinitesimal`
predicates, `near`/`HyperMonad`, and integer powers.

⚠️ NOT ported here — genuinely missing on the Lean side, not just untried:
`sqrt`/`exp`/`log`/`sin`/`cos` (Julia's Taylor-series implementations, which
would need a from-scratch power-series `exp`/`log` in Lean), the `∑`/`∫`
Riemann-sum operators over functions, `taylor_series`, and `Closure`-level `≈`
(function equality sampled at a few points). `Hyper/probes/EvalsDerivatives.lean`
already covers the function-level `∂` (step/spike/Dirac-δ) independently.
-/

open Hypers

namespace Hypers.HyperLists.Probes.Julia

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

end Hypers.HyperLists.Probes.Julia
