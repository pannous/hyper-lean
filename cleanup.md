# Cleanup plan: two probability frameworks side by side

Written before implementing the integral/density reframing requested on
2026-09-12. Records what moves, what becomes stale, and what must not be lost.

## Why

The existing 20 exercises answer "what is the probability of one exact
outcome?" by **counting** a hyperfinite sample space: `Ω = {0,…,ω−1}`, an
`ω × ω` grid for the dart, `P(E) = #E / #Ω`. That is a legitimate model, but it
is not the intended one. The intended framework keeps **ordinary real
intervals** — `[0,1]`, not `{0,…,ω−1}` — and moves all the hyperreal content
into the **integral**: `dx = ε`, so that a point of a uniform law on `[0,1]`
has probability `ε`, and `ω` is the value a density takes at an atom, i.e. the
algebraic Dirac delta.

Both frameworks give `P({y}) = ε` for the unit interval. They differ in what is
primitive (a grid of outcomes vs. a density and an integral) and in what
generalizes (the counting model needs a new grid convention per geometry; the
integral model needs one integral axiom).

## Moves

| From | To |
|------|-----|
| `notes/algebraic-stochastics-exercises.md` | `notes/counting/algebraic-stochastics-exercises.md` |
| `notes/hyperreal-probability-foundations.md` | `notes/counting/hyperreal-probability-foundations.md` |
| `notes/sigma-algebra-not-needed.md` | `notes/counting/sigma-algebra-not-needed.md` |

New: `notes/integral/integral-probability-foundations.md` (theory) and
`notes/integral/integral-probability-exercises.md` (exercises).

Nothing is deleted. The counting exercises and their three checked Lean
modules stay valid and stay built; they are relabeled as one model, not as
*the* framework.

## References to update

- `paper/build_exercises.py` — `SOURCE` path, docstring.
- `notes/counting/hyperreal-probability-foundations.md` — link to the
  exercises (now a sibling).
- `notes/counting/sigma-algebra-not-needed.md` — two `notes/…` paths.
- `Hyper/HyperProbability.lean`, `Hyper/AlgebraicStochasticsIntermediate.lean`
  — doc-comment paths only, no code.

## Becomes stale

- `README.md` sections `integral ε = 1 or 2`, `algebraic δ`, `Probabilities`
  state the integral gauging informally and inconsistently (`∫(-ε,ε)(ω) = 2`
  vs. `∫(0,ε)(ω) = 1`, `δ := ω₀/2`). The new foundations note must pin one
  convention explicitly and say what the other choice would change, rather
  than leave both floating.
- The published papers describe the counting model as *the* framework in their
  opening page. Once the integral exercises exist, the booklets need to say
  which model they are in.

## Not attempted yet (state honestly, do not fake)

- No Lean formalization of the integral. `Hyper/HyperList.lean` has only
  `hint`, a term-level exponent shift; there is no `∫`, no density type, no
  hyperfinite index ranging over `ω` dots. The new exercises must therefore be
  labeled by readiness exactly as the counting ones are, and the **Now** label
  must not be claimed for anything that needs an index set of size `ω`.
- The old exercises' Lean kernels are not ported to the new framing.

## Status 2026-09-12

Done: the moves above, the two new notes, and the paper generator now builds
both curricula (four booklets, light and dark each). Not done, and deliberately
not faked: any Lean formalization of the integral — see §7 of the foundations
note and the **Research** labels.
