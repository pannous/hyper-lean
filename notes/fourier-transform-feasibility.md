# Feasibility: hyperreal ε/ω Fourier transform

Question: can the same trick that gives us an algebraic derivative of the step
function (`∂H = ω` at 0, `δ := ω₀/2`, see README [algebraic δ](../README.md#algebraic-δ))
be reused to define the Fourier transform at points/functions where the
classical integral `F(k) = ∫ f(x) e^{-ikx} dx` diverges?

## Verdict up front

**Mathematically sound, well precedented, not yet built.** Nonstandard analysis
already has a full hyperfinite Fourier transform (Robinson-era; Luxemburg,
Stroyan/Luxemburg, Cutland, Albeverio et al.) that does exactly this: replace
the continuum integral by a hyperfinite Riemann sum over `2ω+1` points spaced
`ε = 1/ω` apart, and take the standard part. Our algebraic ε/ω model is a
first-order shadow of that, so the idea transfers — but three pieces of
infrastructure this repo has for `∂`/`∫`/`δ` don't yet exist for FT, and one
case (superpolynomial growth) plausibly can't be reached at first order at all.

## Why it fits: the mechanism is the same shape

Heaviside/δ trick, restated as a limit-avoidance pattern:
```
H(x) := x ≥ 0            # ordinary predicate, no limit
δ(x) := dH(x)/dx = ω₀/2  # algebraic, no limit either
```
The classical regularization used to *tame* Fourier-breaking functions is the
**Sokhotski–Plemelj formula**:
```
lim_{ε→0+} 1/(x ∓ iε) = P(1/x) ± iπδ(x)
```
This is *already* phrased with an infinitesimal `ε` standing in for a limit —
it's the textbook case begging for our algebraic ε instead of an analytic
limit. That's the strongest sign this generalizes cleanly.

## Case-by-case feasibility against classical FT breakdown modes

| case | classical breakdown | hyperreal fix | feasibility |
|---|---|---|---|
| `f(x)=1` (DC/constant) | not L¹, integral doesn't converge | hyperfinite sum `ε·Σ_{n=-ω}^{ω} e^{-iknε}` is a geometric sum; its standard part is infinite (order ω) in the halo of `k=0` and infinitesimal outside it — literally the same halo-support shape as `ω₀` | **high** — reuses `ω₀`/`δ:=ω₀/2` machinery directly, almost no new theory |
| periodic (`sin`, `cos`, Dirac comb) | FT is a sum of shifted deltas, not a function | same hyperfinite-sum argument repeated at each shifted frequency | **high** — same mechanism, iterated |
| `H(x)` step / `sgn(x)` | FT = `πδ(k) + 1/(ik)` (Cauchy principal value) | δ-part reuses existing step-derivative trick; the `1/(ik)` principal-value part needs a **new operator**: symmetric cancellation of the singular hyperfinite terms around `k=0`, i.e. an algebraic PV, not currently defined anywhere in `Hyper/` | **medium** — half the answer is free, half is new |
| `x^n` (polynomials) | FT = derivatives of `δ(k)` | needs `δ', δ'', …`; README already sketches a 2nd-order spike (`∂(x==0 and ω)(0) = ω²`) as a first-order case of this | **medium-high** — plausible extension of existing sketch, not yet formalized even informally |
| superpolynomial growth (`e^{x²}`, etc.) | FT doesn't exist even as a tempered distribution | hyperfinite sum overflows past order `ω` into `ω²`, `ω³`, … — genuinely needs an asymptotic *hierarchy*, not just first-order `ℝ,ε,ω` | **low at first order** — README's own "First order analysis" section explicitly buckets `ε²,ω²,…` away; this case needs exactly what that section defers |
| conditionally convergent oscillatory integrals (e.g. `x·sin(x)`) | value depends on summation order (Abel/Cesàro) | hyperfinite sum has the *same* order-dependence — README already flags this ambiguity generally (`∫(-ω,ω)(ε)=2` vs. `2ω=ω+ω` under "standard infinity") | **medium-low** — known unresolved ambiguity in the existing model, not a new problem, but not solved either |

## What's actually missing to build this (gaps checked against current code)

1. **No hyperfinite domain-sum integral exists.** The `∫` operator that's
   actually implemented (`Hyper/HyperList.lean:642`) is a *term-level formal
   antiderivative* on monomials — `∫(∑ r·x^e) := ∑ r·x^{e+1}`, so `∫1 = ω`,
   `∫(42ε) = 42`. That is not the same object as a Riemann/hyperfinite sum
   `Σ f(nε)·e^{-iknε}·ε` over an internal domain `[-ω,ω]`. FT needs the
   latter; only the former is built. This is the biggest gap.
2. **No complex numbers in the `Hyper` ring.** `hexp`/`hsin`/`hcos`
   (`Hyper/HyperTranscendental.lean`) are separate real truncated-Taylor
   functions over `R*`; there's no `e^{-ikx} = cos - i·sin` combined
   algebraically inside a single Hyper value. `PiEField.lean` only imports
   `Mathlib.Analysis.Complex.ExponentialBounds` for real bounds, not to
   complexify the coefficient field. Need either `Hyper ⊗ ℂ` or carry
   `(cos, sin)` pairs through the sum by hand.
3. **Standard part already exists and needs no change.** `standard`/`st`
   (`Hyper/HyperList.lean:265`) extracts the order-0 coefficient algebraically
   — exactly the tool needed to read off a finite FT value once the sum above
   exists. Nothing to build here.
4. **`hyper.jl` already has the one thing Lean doesn't: complex coefficients**
   (`const Field = ComplexF64`, `hyper.jl:51`). That makes Julia, not Lean,
   the cheap place to prototype a hyperfinite DFT first — consistent with
   this repo's existing pattern of prototyping in Julia before formalizing.

## Recommended first experiment (cheap, falsifiable)

In `hyper.jl` (which already has `ComplexF64`), compute the hyperfinite DFT of
`f(x)=1` over `n = -ω..ω`, `ε = 1/ω`, and check that `standard(F(k))` behaves
like `2πδ(k)`: infinite (order ω) inside the halo of `k=0`, infinitesimal
outside it. If that lands, it's the FT analogue of `hyper_tests.jl`'s existing
step-function-derivative test, and a template for the `H(x)`/PV case next.
Only after that should this move into `Hyper/*.lean`.

## Open question this doesn't resolve

The order-of-summation ambiguity (`2ω` vs `ω+ω`, README "standard infinity")
is inherited by every FT case that involves an infinite domain, not just the
already-known probability cases. Worth resolving generally rather than
per-application — it will otherwise resurface for every future infinite-sum
extension of this model, not just FT.
