# Why the first algebraic exercises do not start with a σ-algebra

This note is scoped to the executable algebra developed in this repository.
It does **not** claim that σ-algebras are unnecessary for a complete theory of
probability.

The initial framework begins with explicitly constructed events and symbolic
counts. For a uniform sample space,

```text
P(E) = count(E) / count(Ω),
```

where the counts may contain powers of `ω` and simplify algebraically using
`εω = 1`. Finite complements, disjoint unions, independent products,
conditional ratios with proved denominators, and finite expectations can all
be studied directly from those values. A separate measurability predicate is
not needed for these deliberately finite, constructed exercises.

That limited observation must not be inflated into a general theorem. The
current `HyperList` representation has no internal sets, transfer principle,
saturation, genuinely hyperfinite index type, or Loeb construction. It cannot
justify countable additivity, arbitrary infinite unions, almost-sure
convergence, or classical limit theorems merely because `ε` and `ω` occur in
its formulas. Definability in Lean also does not make every event part of a
coherent probability assignment.

Thus there are two separate developments:

1. **Current algebraic scope:** explicitly represented events, normalized
   symbolic counts, and finite probability identities in `R*`.
2. **Future analytic scope:** a sound event space with the closure and
   convergence structure required for countable probability laws, or a
   genuine nonstandard universe from which a classical probability space can
   be recovered.

The first scope is enough for the exercise progression in
`notes/algebraic-stochastics-exercises.md`. The second remains future work.
See `notes/hyperreal-probability-foundations.md` for the precise framework
boundary and implementation roadmap.
