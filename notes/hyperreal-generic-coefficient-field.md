# Making the coefficient field genuinely extensible from outside

`Hyper/HyperGeneric.lean`, implemented 2026-08-26. Corrects the shape of
the previous pass: `Hyper/HyperQuadField.lean` got `Quad d`-coefficient
hyperreals by hand-copying `HyperList.lean`'s term/`simplify`/`merge`/`Mul`
machinery into a second file. That's the wrong move — it means every new
coefficient field needs its own hand-adapted copy of the same construction.
The actual ask: the coefficient field should be **extensible from outside**,
the same way `ε`/`ω` are just generators anyone builds on top of, not
something requiring the whole machinery re-derived per field.

## What changed

`GHyper F` (`Hyper/HyperGeneric.lean`) is generic in the coefficient type
`F`, constrained only by the six instances the construction actually needs:
`Zero`, `One`, `Add`, `Neg`, `Mul`, `DecidableEq`. `simplify`/`merge`/`Mul`/
`ε`/`ω` are written **once**. Supplying `F := ℚ` reproduces
`HyperList.lean`'s arithmetic; supplying `F := Quad d`
(`Hyper/QuadField.lean`) reproduces `HyperQuadField.lean`'s irrational
coefficients — through the identical code, not a second copy of it. Both
instantiations are checked against the same facts proved for
`HyperQuadField.lean` (`ε·ω=1`, `√2·√2=2`, `√2·ε·ω=√2`), confirming the
generic version isn't a weaker stand-in.

One structural note worth keeping: `myle`, the sort/merge key, only ever
inspects the *exponent* (fixed at `ℚ`), never the coefficient `F` — so none
of `simplify`/`merge`/`Mul`/the generators need `F` to have an order at all.
An order on `GHyper F` itself (comparing hyperreal *values*, the
`leadSign`/`<`/`≤` machinery `HyperList.lean` has) would need `F` to supply
one too; not attempted here, matching the scope `HyperQuadField.lean`
already stopped at.

## Where this leaves `HyperQuadField.lean`

It's now redundant — `GHyper (Quad d)` does the same job through the
generic construction. Left in place rather than deleted (it's small,
correct, and still directly readable on its own); worth revisiting whether
to remove it once/if something else depends on picking one. Not removed
unprompted here.

## The remaining honest limits, unchanged from before

- `Quad d` still can't contain π or e (transcendence — see
  `Hyper/QuadField.lean`'s header); that boundary is about `Quad`
  specifically, not about `GHyper` being generic.
- `Hyper/HyperConstants.lean`'s π/e exponent-track extension and
  `Hyper/HyperQuadConstants.lean`'s combination of the two still stand as
  they were — `GHyper F`'s genericity is about the coefficient slot, not a
  replacement for the exponent-track mechanism.
