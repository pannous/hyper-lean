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

**(I) Integral.** For `f : ℝ → R*`,

```text
∫_[a,b) f(x) dx  :=  Σ_{k=0}^{(b−a)ω − 1} f(a + kε) · ε
```

— a hyperfinite left-endpoint Riemann sum with `dx = ε`, **evaluated in `R*`
and not followed by `st`**. The classical integral is recovered as
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

because then `P({y}) = ∫_dot(y) p = a·ω·ε = a` exactly. The Dirac delta is the
density of the unit atom,

```text
δ_y(x) := ω  if x ∈ dot(y),  else 0,        ∫_ℝ δ_y = 1.
```

This is the README's rule `π(x)=a ⟺ p(x)=a·ω`, now stated as the definition of
what an atom *is*.

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

The README currently states several of these in mutually inconsistent forms.
This note fixes the first column; the third column is what changes if you
prefer the alternative.

| choice | fixed here | alternative and its cost |
|---|---|---|
| interval type | half-open `[a,b)` | closed `[0,1]` has `ω+1` dots, so `∫_[0,1] 1 = 1 + ε`; a uniform law on it needs `p = 1/(1+ε) = 1 − ε + ε² − …` and then `P({0}) = ε − ε² + …` |
| sample point | left endpoint | midpoint kills the `ε/2` bias in `E[X]`; right endpoint flips its sign |
| `∫ δ` | `δ = ω` on one dot, `∫δ = 1` | the README's symmetric halo `(−ε,ε)` spans two dots, giving `∫ω = 2` and forcing `δ := ω₀/2` |
| ambient line | `[−ω, ω)`, `∫1 = 2ω` | one-sided `ƒ = ∫_[0,ω)`, `ƒ1 = ω`, the README's `π` vs `τ` remark |
| `st` | applied never, except when explicitly asked for | applying it eagerly collapses this whole framework to the classical one |

None of these is forced by the algebra. All of them must be *stated*, because
each changes answers at order `ε` — which is exactly the order this framework
exists to talk about.

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

## 7. Status: what is *not* done

Honestly scoped, because none of it is hidden in the exercises:

- **No Lean formalization.** `Hyper/HyperList.lean` has `hint` (a term-level
  exponent shift) and nothing else relevant. There is no `∫`, no density type,
  and above all **no index type of size `ω`** to sum over. Every exercise that
  needs `Σ_{k<ω}` is therefore *Research*, not *Now*, no matter how short its
  algebra is.
- **`st(∫f) = ∫_classical f` is assumed, not proved.** Proving it needs a
  transfer principle or an explicit convergence argument, neither of which
  exists in this repository.
- **Countable additivity is not claimed.** Summing `ε` over `ω` dots is a
  hyperfinite sum, not a countable one; `notes/counting/sigma-algebra-not-needed.md`
  applies verbatim here.
- **`2^ω`, `e^{−λ}` inside the integral** need
  `Hyper/HyperTranscendental.lean` to be connected to this machinery; it is
  not.

The exercises are in
[`integral-probability-exercises.md`](integral-probability-exercises.md).
