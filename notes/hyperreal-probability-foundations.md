# Reformulating probability theory on `R*`, without measure theory

Written 2026-08-26, prompted by: "think deeply how we can reformulate the whole
basis of probability theory with this mechanism... avoid the whole notion of
measure and replace it with the simple algebraic hyper approach... we don't
care too much about Sigma algebra but maybe they're still necessary."

Concrete anchor: `Hyper/DartPointProbZero.lean` (point/line-in-a-disc, proved)
and its new generalization `Hyper/HyperProbability.lean` (`regionMass`,
arbitrary codimension `k`, proved for all `k` not just 1 and 2). The abstract
axiomatic sketch this replaces is `Hyper/old/HyperProbability.lean`.

## 1. What the dart example actually demonstrates

Classically, a dart landing uniformly on a disc: `P(hits exact point) = 0`,
`P(hits exact line through the disc) = 0`. Both are "measure zero", both get
treated as impossible — but a point and a line are not equally impossible.
A line is obviously, combinatorially, far more likely to be hit than one
exact point. Classical measure theory has **no vocabulary** for this: `0 = 0`,
end of story. That's the real defect, not just the philosophical discomfort
of calling a possible event "impossible."

The hyperreal fix already proved in this repo: `pointMass A = ε²/A`,
`lineMass L A = L·ε/A`. Both are positive (genuinely possible), both have
standard part 0 (classical theory recovered as the "shadow"), and critically
`pointMass A < lineMass L A` for any `L, A > 0` — the order structure of `R*`
recovers the lost information. `Hyper/HyperProbability.lean` now proves this
**for every codimension gap, not just point-vs-line**: `regionMass_mono` says
a higher-codimension region loses to a lower-codimension one regardless of
how much bigger its ordinary content is. So instead of a flat classical
`{measure zero, positive measure}` split, you get a genuine **total order of
infinitesimal-smallness classes** — order 0 (appreciable), order 1, order 2,
... — and every classically-"impossible" event lands in exactly one class,
comparably.

## 2. The core primitive: codimension-indexed atom mass, not a measure

A classical measure `μ : Σ → [0,1]` is a *function on sets*, built by
integrating a density (or defined directly), satisfying countable additivity.
The hyperreal replacement here is not another such function — it's an
algebraic **unit conversion**: fix an ambient space of "dimension" `n`
(equivalently, a resolution `ω = 1/ε`, per the Readme's `ωⁿ·εⁿ = 1` gauging
law), and say that a region of codimension `k` (i.e. `n - k`-dimensional)
and ordinary content `c` — a length, an area, a count, computed by whatever
ordinary standard-real geometry or combinatorics fits the region — has
probability

```
regionMass c k A = c · εᵏ / A
```

`A` is the ambient space's own total ordinary content (so the whole space,
`k = 0`, gets probability `A/A = 1`, appreciable — as it must). This is
*constructed*, not posited: `εᵏ` really is `ε * ε * ⋯ * ε` (`hpow` in the
Lean file), so "atom mass" literally means "one cell of a hyperfinite grid
with `ωᵏ` cells packed into the codim-`k` slice." No integral, no σ-algebra,
no limit — just ordinary real-valued geometric/combinatorial content,
multiplied by a fixed infinitesimal unit determined by codimension. This is
exactly the Readme's `εᵚ` idea (*"εᵚ for each σ-algebra Ω such that ∫εᵚ=1
over uncountable Ω and ∑εᵚ=1 for countable Ω"*), made concrete: the "Ω" that
matters is not a σ-algebra, it's just the ambient dimension/resolution.

## 3. Do we still need σ-algebras? — No, not for internal reasoning

A σ-algebra earns its keep in classical theory for two reasons:

1. **Not every set has an obvious "size."** Under choice, pathological sets
   (Vitali sets) exist with no consistent measure at all — so you restrict
   attention to a closed family (the σ-algebra) on which a measure *can* be
   defined.
2. **Countable additivity needs a home.** Limits of countable unions have to
   land back inside the family you're allowed to measure.

Neither problem survives translation into this algebraic setting:

- **Every region here is defined by an ordinary geometric/combinatorial
  description** (a point, a segment of length `L`, a disc of radius `r`,
  a finite union of such things) — never by an unconstructive
  choice-theoretic diagonalization. `c` is just "the ordinary content of this
  region," computed the normal way; there is no pathological case to guard
  against inside a Lean formalization that never invokes choice to construct
  the set in the first place. This mirrors Nelson/Loeb nonstandard analysis:
  **every internal subset of a hyperfinite set is automatically
  "measurable"** — measurability stops being a separate condition to check
  and becomes automatic from the construction.
- **You never take a literal countable limit inside `R*`.** Every union of
  regions you'd actually form (finitely many points, finitely many line
  segments, ...) is a *finite* union, and finite additivity is just `+` on
  `R*` — already proved, already computable (`merge` in
  `Hyper/HyperList.lean`). Countable additivity as a *separate axiom* is a
  classical-analysis requirement for handling genuine infinite limits; it has
  no work to do here because the infinitesimal/infinite structure is carried
  by `ε`/`ω` *algebraically*, not by a limiting process.

So: **inside `R*`, skip σ-algebras entirely.** Replace "measurable set" with
"region with an ordinary-geometry content `c`", and finite additivity is
free. A σ-algebra only re-enters if/when you want to push a result **back
down** to classical probability — e.g. to say "the standard part of this
hyperreal probability is a genuine Kolmogorov probability measure." That's
exactly the content of **Loeb's theorem**: the standard part of a hyperfinite
counting measure *is* countably additive, and the σ-algebra it lives on (the
Loeb σ-algebra) is *generated automatically* by that construction — you never
hand-pick it. `st` is already implemented (`Hyper/HyperList.lean`); a full
Loeb-measure formalization is not attempted here (see §6), but the point
that matters for design purposes: **σ-algebras are a classical-side
artifact of the standard-part map, not a prerequisite for defining
hyperreal probabilities in the first place.**

## 4. Discrete and continuous distributions become the same object

The Readme's own "No pointweight" section already has the key unification
insight, worth stating plainly: classical theory needs two separate
mechanisms — a density function for the continuous part of a distribution,
and ad hoc point weights bolted on for atoms (e.g. "P(X=0) = 0.3, and
otherwise X is uniform on [0,1]"). Here, a classical atom of mass `a` at
point `x` is nothing but **a density spike of order `ω`** at `x`:
`p(x) = a·ω`, and every distribution — discrete, continuous, or mixed — is
just `F = ∫p` for a single, uniformly-typed density function `p : R* → R*`.
No case split. The algebraic Dirac delta and Heaviside step already exist
(`Hyper/probes/EvalsDerivatives.lean`'s `H`/`spike`/`deriv`), so the atoms of
this picture are not a future task — they're a fact about the derivative
operator already proved.

## 5. What a full build-out needs — scoped honestly

- **Region algebra and `regionMass` (done).** `Hyper/HyperProbability.lean`:
  `regionMass c k A`, generalizing `pointMass`/`lineMass`, with the general
  monotonicity theorem proved for all codimension gaps. Finite additivity
  over disjoint regions of the *same* codimension is immediate from `R*`'s
  `+` (e.g. two disjoint points: `pointMass A + pointMass A` is just
  `2 · pointMass A` by `HSMul`) — worth a follow-up lemma, but mechanical.

- **Expectation, and hence random variables, needs a general `∑`/`∫`
  operator over functions — still missing.** `hyper.jl` has one
  (`∑(f::Function) = ...`), and `Hyper/HyperList.lean` has the *term-level*
  `hint`/`hderiv` (shifting one monomial's exponent — correct for `∫x = x²/2`
  but not a Riemann-sum operator over an arbitrary function). This is the
  single biggest missing piece to go from "probabilities of individual
  regions" to "expectation of a random variable," and it's a real, scoped
  task: define `∑ (f : R* → R*) (n : ℕ) : R*` as a finite sum with `n` a
  parameter that can be instantiated at genuinely large values (up to
  whatever `ω`-order behavior you want to exhibit), then `E[X] := ∑ x · p(x)`
  over the grid, matching `hyper.jl`'s own construction. Flagged, not
  attempted here — this conversation was scoped to design, not a multi-day
  formalization sprint.

- **Independence is easy, algebraically**: `P(A ∩ B) = P(A) · P(B)` is just
  `R*` multiplication, and for regions built as products of independent
  grids (e.g. two independent darts), the atom-mass counting argument that
  proves it is finite combinatorics — arguably *easier* than the classical
  product-measure construction, not harder.

- **Conditional probability has a genuine open problem: `R*`'s `Field`
  instance is incomplete.** `P(A|B) = P(A∩B)/P(B)` needs division, and
  `Hyper/HyperList.lean`'s `Inv`/`Field` instance is exact only for
  single-monomial values (`mul_inv_cancel := sorry` for general multi-term
  `R*`, documented as structurally hard — finite-support "Laurent series"
  genuinely aren't a field). This is fine whenever `P(B)` happens to be a
  pure `εᵏ`-order value (the common case for symmetric problems — a single
  point, a single line, a single codimension-`k` cell), which is exactly
  where `Inv` already works. It breaks for `B` a *mixed-order* union (e.g.
  "hit this point or this line") because summing a `εᵏ` term and an `εʲ`
  term produces a genuine two-term `R*` value, and dividing by that isn't
  well-defined here. Two ways forward, neither attempted yet: (a) work with
  **leading-order conditional probability** — condition using only `B`'s
  dominant term, which is what a working mathematician does anyway when
  eyeballing "to leading order, given a rare event, ..." — or (b) chip away
  further at the `Field R*` gap (already flagged as hard in
  `Hyper/HyperList.lean`'s own comments, not something to reopen casually).

- **Limit theorems (LLN, CLT) are out of scope for now.** These are
  genuinely the hardest part of classical probability, and the nonstandard
  route to them (Nelson's "Radically Elementary Probability Theory", or full
  Loeb measure) is real, substantial machinery — internal set theory,
  hyperfinite index sets distinct from any Lean `Fin n`, and a transfer
  principle this project's concrete `List (ℚ × ℚ)` model doesn't have (it's
  a formal-algebra model, not a genuine nonstandard-universe ultrapower — see
  §7). The Readme itself flags Herzberg's radically-elementary approach as
  *"too general, waste of precision"* for this project's goals; that verdict
  still seems right. Recommendation: don't attempt LLN/CLT against this
  concrete model — they'd need a different, heavier foundation than `R*`'s
  `List (ℚ × ℚ)` term list.

## 6. Loeb measure, deliberately not built

Loeb's construction — push a hyperfinite counting measure on an *internal*
algebra down through `st` to get a genuine countably-additive measure on a
σ-algebra generated by that process — is the standard way nonstandard
analysis recovers classical probability theory as a special case, and it's
the rigorous justification for treating `st(regionMass ...) = 0` as "this
really does recover classical measure theory," not just a suggestive
coincidence (`point_prob_standard_zero`/`line_prob_standard_zero` already
prove the `st = 0` half). A full formalization is a serious undertaking
(internal sets, an actual ultrafilter/transfer principle) and isn't
warranted unless a concrete question needs it — the design conclusion in §3
(σ-algebras are unnecessary *for reasoning inside `R*`*) doesn't depend on
formalizing Loeb's theorem, only on citing that it exists as the reason
pushing back down to classical theory is safe.

## 7. A honesty check on what `R*` actually is

Worth being explicit about, since it bounds what's realistically buildable:
`Hyper/HyperList.lean`'s `R*` is a concrete algebraic gadget — finite lists
of `(coefficient, rational exponent)` pairs, with `ε`/`ω` as formal
generators satisfying `ε·ω = 1`. It is **not** a nonstandard-universe
ultrapower `*ℝ` with a genuine transfer principle, internal sets, or
hyperfinite index sets bigger than any Lean `Fin n`. Everything in §§1–4
above works *because it only needs ordinary algebra on this concrete
structure* (comparing exponents, multiplying formal series, `st` as a
plain filter) — it never needs "for every internal formula φ, φ holds
standardly iff it holds nonstandardly," which is the actual content of
transfer and is not available here. That's precisely why §5's LLN/CLT item
is marked out of scope rather than merely hard: those results are proved
*using* transfer/internal-set machinery in the nonstandard literature, and
porting them would mean building that machinery first, not extending `R*`.
Region-mass-style results (comparing infinitesimal orders, finite sums,
finite products) stay comfortably inside what `R*` actually provides.

## 8. Bottom line

- Kolmogorov's axioms (σ-algebra + countably-additive measure) get replaced
  by: ordinary real-valued content `c` for a region, times `εᵏ` for its
  codimension `k`, divided by the ambient total content `A`. Finite
  additivity is free (`R*`'s `+`); countable additivity's job (coherence
  under limits) is absorbed into the algebra of `ε`/`ω` and never separately
  needed inside `R*`.
- σ-algebras are not necessary for defining or computing probabilities this
  way. They reappear only as the classical-side σ-algebra Loeb's theorem
  generates when you push a result down via `st` — which is a fact you can
  cite, not a structure you need to build, unless a specific question
  requires the classical-recovery direction to be airtight.
- The framework scales cleanly to arbitrary codimension (proved, this
  session) and unifies discrete/continuous distributions via density spikes
  (already implicit in the existing `∂`/Dirac-delta machinery). Expectation
  (needs a general `∑`/`∫`), conditional probability across mixed-order
  events (blocked on `Field R*` completeness), and limit theorems (need
  machinery `R*` doesn't have) are the honestly-scoped remaining gaps, not
  glossed over.
