# Why σ-algebras aren't needed for hyperreal probability

Extracted 2026-08-26 from `notes/hyperreal-probability-foundations.md` §3, on
its own because it's the load-bearing insight of that whole reformulation:
**σ-algebras are a classical-side artifact, not a prerequisite.**

## The classical justification for σ-algebras

A σ-algebra Σ ⊆ 2^Ω earns its keep for two reasons, and only two:

1. **Not every set has an obvious "size."** Under the axiom of choice,
   pathological sets exist (Vitali sets) with no consistent measure at all.
   You restrict attention to a closed family — the σ-algebra — on which a
   measure *can* be consistently defined, and call everything outside it
   "non-measurable."
2. **Countable additivity needs somewhere to live.** Limits of countably
   many unions have to land back inside the family you're allowed to
   measure, or the whole apparatus of limits/convergence in probability
   (a.s. convergence, martingales, ...) has nowhere to stand.

## Why neither reason survives translation to `R*`

Replace "measure" with the algebraic construction already proved in this
repo (`Hyper/DartPointProbZero.lean`, generalized in
`Hyper/HyperProbability.lean`): a region of codimension `k` and ordinary
content `c`, in an ambient space of total content `A`, gets probability
`c · εᵏ / A`. Both classical justifications for a σ-algebra evaporate:

- **Every region here is built from an ordinary geometric or combinatorial
  description** — a point, a segment of length `L`, a disc of radius `r`, a
  finite union of such things — never from an unconstructive
  choice-theoretic diagonalization. There is no pathological set to guard
  against, because nothing in this framework can *produce* one: `c` is just
  "the ordinary content of this region," computed the normal way. This is
  the same move nonstandard analysis makes with **internal sets**: every
  internal subset of a hyperfinite set is automatically well-behaved.
  Measurability stops being a condition you check against a pre-chosen
  family and becomes automatic from how the set was built.

- **You never take a literal countable limit inside `R*`.** Every union
  you'd actually form in this setting — finitely many points, finitely many
  line segments — is a *finite* union. Finite additivity is just `+` on
  `R*` (`merge` in `Hyper/HyperList.lean`), already proved, already
  computable. Countable additivity is a requirement for taming genuine
  infinite limits taken *inside the reals*; here the infinite/infinitesimal
  structure is carried *algebraically* by `ε`/`ω` from the start, so there's
  no limit left for countable additivity to referee.

## Where a σ-algebra can legitimately reappear

Only on the way back down. If you want to say "the standard part of this
hyperreal probability is a genuine, classical, countably-additive
probability measure," that claim is exactly the content of **Loeb's
theorem**: the standard part of a hyperfinite counting measure *is*
countably additive, on a σ-algebra (the Loeb σ-algebra) that the
construction *generates automatically*. You never hand-pick it — it falls
out of pushing through `st`. `st` is already implemented
(`Hyper/HyperList.lean`); `point_prob_standard_zero`/
`line_prob_standard_zero` in `Hyper/DartPointProbZero.lean` already prove the
"`st = 0`, classical theory recovered" half concretely. A full Loeb-measure
formalization (which would need genuine internal-set/transfer-principle
machinery this repo's concrete `List (ℚ × ℚ)` model doesn't have — see the
honesty check in `notes/hyperreal-probability-foundations.md` §7) is not
needed to *use* this fact, only to *prove it in general* — and nothing in
the region-mass framework depends on having that general proof in hand.

## The one-line version

**A σ-algebra is the classical answer to "which sets can I trust to have a
size?" — and in the hyperreal-algebraic setting, every region you can write
down already has one, by construction, so the question never comes up. It
only comes back if you ask a *different* question: "does the shadow of my
hyperreal answer land back in classical probability theory?" — and that
question has its own, separate, already-known answer (Loeb), not a
prerequisite for doing the hyperreal probability in the first place.**
