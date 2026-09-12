# Probability on ordinary intervals, with the hyperreal integral doing the work

Started 2026-09-12. This is the intended framework: **keep the ordinary real
interval `[0,1]`**, do not replace it by a hyperfinite sample space
`{0,…,ω−1}`, and put all the hyperreal content into the **integral** and the
**density**. The counting model in `notes/counting/` remains valid but is a
different, more special-purpose device.

The one answer this framework must deliver:

```text
X uniform on [0,1]  ⟹  P(X = y) = ε        (not 0, not "0 but not impossible")
```

Everything below is arranged so that this is a one-line consequence of the
integral axiom rather than an extra postulate.

## 1. What is primitive

| | counting model | this model |
|---|---|---|
| sample space | `Ω = {0,…,ω−1}`, a hyperfinite set | `[0,1] ⊂ ℝ`, an ordinary interval |
| primitive | `P(E) = #E / #Ω` | `P(E) = ∫_E p(x) dx` |
| a point is rare because | there are `ω` outcomes | `dx = ε` |
| an atom of mass `a` | `aω` outcomes | density value `p = aω` |
| generalizes by | choosing a grid per geometry | choosing a density |

## 2. Axioms

**(G) Gauge.** `ε > 0` is infinitesimal, `ω := 1/ε`, so `εω = 1`. As in the
rest of the project, this is the *canonical* infinitesimal, not an arbitrary
one.

**(D) Dot resolution.** The real line is covered, without overlap, by the
half-open *dots*

```text
dot(x) := [x, x+ε).
```

A point `y ∈ ℝ` is identified with `dot(y)`. A half-open interval `[a,b)` of
standard length `b−a` is the disjoint union of exactly `(b−a)·ω` dots. The
half-open convention is a choice and it is the one that makes the counts come
out exactly; §5 records what the other choices cost.

**(I) Integral.** For `f : ℝ → R*` and a sample offset `s ∈ [0,1]`,

```text
∫_[a,b) f(x) dx  :=  Σ_{k=0}^{(b−a)ω − 1} f(a + (k+s)ε) · ε
```

— a hyperfinite Riemann sum with `dx = ε`, **evaluated in `R*` and not
followed by `st`**. Canonically `s = ½`, the midpoint (symmetric) rule, which
pairs with the symmetric difference quotient; `s = 0` and `s = 1` are the left
and right rules and differ from it only at order `ε` (§5). The classical integral is recovered as
`st(∫ f dx)` whenever `f` is standard and Riemann integrable; see §5 for the
part of this claim that is currently an assumption rather than a theorem here.

**(P) Probability as density.** A distribution on a region `S` is a density
`p : S → R*` with `p ≥ 0` and `∫_S p(x) dx = 1`. Then `P(E) := ∫_E p(x) dx`.
There are **no separate point weights** — see (A).

**(A) Atoms are `ω`-valued densities.** A classical atom of mass `a` at `y` is
not an extra ingredient; it is the density value

```text
p(y) = a·ω      (and p ordinary elsewhere),
```

because then `P({y}) = ∫_dot(y) p = a·ω·ε = a` exactly. This is the README's
rule `π(x)=a ⟺ p(x)=a·ω`, now stated as the definition of what an atom *is*.

**The Dirac delta is this same object**, not a second one: `δ_y := 1·ω` on
`dot(y)`, so `∫δ = 1` and `a·δ_y` is the atom of mass `a`. This is exactly the
unification `ω` was introduced for — one value, one mechanism, no point
weights and no distributions. §5 treats the one place where a *2ε-wide
difference stencil* produces something else.

## 3. The immediate consequences

Uniform on `[0,1)`, i.e. `p ≡ 1`:

```text
∫_[0,1) 1 dx  = ω·ε = 1                       total mass is exactly 1
P({y})        = 1·ε = ε          > 0          ← the required answer
P([c,d))      = d − c                         ordinary lengths survive
st(P({y}))    = 0                             the classical shadow
P(r points)   = r·ε
```

Nothing was counted. `ε` appears because `dx = ε`, and `P({y}) = p(y)·ε` is
just the integral over a single dot. The general rule is worth displaying:

```text
P({y}) = p(y) · ε           for any density p at any point y.
```

So the *order* of a point's probability reads off the density directly:
`p(y)` finite ⟹ `P({y}) ≍ ε`; `p(y) = aω` (an atom) ⟹ `P({y}) = a`, finite;
`p(y) = cε` (a spread-out law, §4) ⟹ `P({y}) = cε²`.

**The dart, without a grid.** On the unit square with `p ≡ 1`, the product
integral has `dA = dx dy = ε²`, so

```text
P(one point)          = ε²
P(the segment {y=x})  = ∫_0^1 P(Y = x) dx = ∫_0^1 ε dx = ε
ratio                 = ω.
```

The codimension hierarchy of `notes/counting/` is recovered as a theorem about
integrals instead of a grid convention: each integration that is *not*
performed costs one factor of `ε`.

**Uniform on the whole line.** With the ambient line `[−ω, ω)` (the README's
`∫1 = 2ω`), a uniform density must be `p ≡ ε/2`, hence

```text
P({y}) = (ε/2)·ε = ε²/2,      P([a,b)) = (b−a)·ε/2.
```

A point of a uniform law on `ℝ` is therefore *second order* rare — strictly
rarer than a point of a uniform law on `[0,1]`. That is a real prediction of
this framework, and it is what the README's undecided `P(x=y) = εᵚ` was
reaching for.

## 4. Expectation, and why the convention is visible

```text
E[g(X)] := ∫ g(x) p(x) dx.
```

For `X` uniform on `[0,1)`, the left-endpoint sum gives exactly

```text
E[X]   = Σ_{k<ω} kε·ε = ε²·ω(ω−1)/2 = 1/2 − ε/2,
E[X²]  = 1/3 − ε/2 + ε²/6,
Var(X) = 1/12 − ε²/12.
```

The `−ε/2` is not an error; it is the exact statement that the left-endpoint
rule samples each dot at its left edge. The midpoint rule
`f(a + (k+½)ε)` gives `E[X] = 1/2` exactly. **Both are consistent; they are
different integrals**, and they agree after `st`. This is the precise form of
the user-visible question "it is not even clear exactly which integral": the
choice is invisible classically and visible here, at order `ε`.

## 5. The conventions that must be pinned (and what each costs)

These are genuine choices, not errors to be corrected — the README's
statements about them are consistent (see below). This note fixes the first
column; the third column is what changes if you prefer the alternative.

| choice | fixed here | alternative and its cost |
|---|---|---|
| interval type | half-open `[a,b)` | closed `[0,1]` has `ω+1` dots, so `∫_[0,1] 1 = 1 + ε`; a uniform law on it needs `p = 1/(1+ε) = 1 − ε + ε² − …` and then `P({0}) = ε − ε² + …` |
| sample point | midpoint, `f(a+(k+½)ε)` | left endpoint biases `E[X]` to `1/2 − ε/2`, right endpoint to `1/2 + ε/2`; the difference is exactly `ε(f(b)−f(a))`, and all three agree after `st` |
| ambient line | `[−ω, ω)`, `∫1 = 2ω` | one-sided `ƒ = ∫_[0,ω)`, `ƒ1 = ω`, the README's `π` vs `τ` remark |
| `st` | applied never, except when explicitly asked for | applying it eagerly collapses this whole framework to the classical one |

None of these is forced by the algebra. All of them must be *stated*, because
each changes answers at order `ε` — which is exactly the order this framework
exists to talk about.

### The `δ` conventions are consistent, and `δ` is the atom

The README's two statements

```text
∫(−ε,ε) ω = 2        ∫(0,ε) ω = 1
```

are the *same* rule applied to two widths: the halo `(−ε,ε)` is two cells wide,
one cell is one cell wide. There is nothing to reconcile, and both are about
the **constant** `ω`, not about `δ`.

`δ` itself is the unit atom — `ω` on a point's cell, mass `1` — and the atom of
mass `a` is `a·δ`. One object. That is precisely the unification `ω` buys:
a discrete mass and a continuous density are values of the same density
function, differing only in order.

**Where the `/2` really comes from.** Apply the symmetric difference quotient,
the one the Julia implementation uses, to the Heaviside step:

```text
∂f(x)  = (f(x+ε) − f(x−ε)) / 2ε
∂H(−ε) = (H(0) − H(−2ε))/2ε = ω/2
∂H(0)  = (H(ε) − H(−ε)) /2ε = ω/2        ⟹ ∂H = ω₀/2,  ∫∂H = 1
```

so `δ := ω₀/2` is right *for that operator*: its stencil is `2ε` wide while
the jump is a point, so it returns `δ` **convolved with the stencil** — the
same mass, spread over two cells instead of one. With the one-sided quotient
`(f(x+ε)−f(x))/ε` the same step gives `ω` on a single cell, which is `δ` on the
nose.

The two agree on mass and on every halo-aligned integral; they differ only if
you integrate over *half* a halo, which is asking a question below the
resolution the theory claims to answer. The implementation keeps them apart by
one boolean (`Spike.stencil`) so that `∂H` can be represented faithfully, but
`dirac = atom · 1` holds definitionally.

So: nothing forces a probability atom and `δ` apart. What is genuinely
two-celled is the *central difference operator*, not the delta.

## 6. What this buys over the counting model

1. The objects stay ordinary: `[0,1]`, densities, integrals. No hyperfinite
   sample space has to be constructed or justified per geometry.
2. One axiom (I) replaces a grid convention per problem.
3. Atoms and continuous parts live in *one* object, the density, so mixed
   distributions need no case split and no point-mass bookkeeping —
   `F = ∫p` always.
4. The Dirac delta stops being a distribution-in-the-Schwartz-sense and
   becomes a value, `ω`.
5. Derivatives and integrals are the same algebra: `∂H = ω` on one dot, and
   `∫∂H = 1`, so the fundamental theorem holds on the nose for the step
   function.

## 7. Status: what is implemented, and what is not

**Implemented and machine-checked** in `Hyper/HyperIntegral.lean`, with
executable checks in `Hyper/probes/IntegralExamples.lean`
(`lake env lean Hyper/probes/IntegralExamples.lean`):

- The integral itself, exactly, for elementary densities (polynomial part plus
  spikes) over hyperreal bounds — including the reals, `[−ω, ω)`.
  There is still no index type of size `ω`; instead the hyperfinite sum is
  evaluated in closed form by the power-sum recursion
  `(p+1)S_p(M) = M^(p+1) − Σ_{j<p} C(p+1,j)S_j(M)`, which is exact for a
  hyperreal bound `M = (b−a)ω` and needs only `R*` arithmetic. Polynomial
  densities of any degree therefore integrate exactly, ε-corrections included.
- All three sampling conventions (`leftRule`, `midRule`, `rightRule`) and the
  exact relation between them.
- `∫_[0,1) 1 = 1`, `∫_ℝ 1 = 2ω`, `∫(−ε,ε) ω = 2`, `∫(0,ε) ω = 1`, `∫δ = 1`.
- `dirac = atom · 1` definitionally, and the central-difference `stepDerivative`
  agrees with it on every halo-aligned integral while differing on a half-halo.
- `P({y}) = p(y)·ε`, checked for the uniform law on `[0,1)` (`ε`), on the whole
  line (`ε²/2`), for the triangular density, and for a mixed atom-plus-uniform
  law.
- Moments: `E[X] = 1/2` (midpoint) against `1/2 − ε/2` (left), and
  `E[X²] = 1/3 − ε²/12` against `1/3 − ε/2 + ε²/6`.

**Not implemented:**

- Products, so no two-dimensional integral yet: the dart and the diagonal
  (Exercises 10, 11) are computed by hand, not by the code.
- Transcendental densities: `Hyper/HyperTranscendental.lean` has `hexp` but it
  is not connected to the integral, so the exponential law is still Research.
- `st(∫f) = ∫_classical f` is assumed, not proved. Proving it needs a transfer
  principle or explicit continuity estimates, neither of which exists here.
- Countable additivity is not claimed. Summing over the dots of an interval is
  a hyperfinite operation, not a countable one;
  `notes/counting/sigma-algebra-not-needed.md` applies verbatim.
- The inverse of a multi-term denominator is still inexact, so the
  renormalization `1/(1+ε)` of Exercise 4 remains a series statement.

The exercises are in
[`integral-probability-exercises.md`](integral-probability-exercises.md).
