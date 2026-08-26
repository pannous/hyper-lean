# `Hyper/PiEField.lean`: from a disconnected axiom to a working normalizer

Written 2026-08-26. Records two fixes made to `Hyper/PiEField.lean` in the
same session: replacing an unsound "shortcut" axiom with a real normalizer,
and a genuine bug found and fixed along the way.

## The starting point: `axiom ratFunField : Field RatFun`

An earlier version represented `ℚ(π,e)` as a bare AST (`RatFun`: `rat`,
`piAtom`, `eAtom`, `add`, `neg`, `mul`, `inv`) with no normalizer, and
asserted `axiom ratFunField : Field RatFun` as a "we'll prove it's a field
later" shortcut. Investigated directly rather than just reading it:

- The axiom is **not** logically inconsistent by itself — some field
  structure provably exists on any countably-infinite set (`RatFun` is one),
  so the bare existence claim is true.
- But it's **disconnected** from the actual executable operations: nothing
  ties the axiom's abstract field structure to the concrete
  `RatFun.add`/`RatFun.mul` constructors `GHyper RatFun`/`#eval`/etc. all use.
  Confirmed concretely: `#eval (pi * pi⁻¹ : RatFun) == 1` and
  `#eval (pi + e : RatFun) == (e + pi : RatFun)` both evaluate to `false`,
  despite the `Field` instance being in scope — trying to invoke
  `mul_comm pi e` even produces a type mismatch, because it resolves against
  a *different* `Mul` instance than plain `*` does (a genuine diamond).
- Separately, `axiom pi_e_algebraicIndependent : AlgebraicIndependent ℚ
  piEReal` asserted a real open problem in number theory (whether π and e
  are algebraically independent — nobody knows) as an established fact.
  Contradicts the principle from `Hyper/PiEField.lean`'s own header on why
  free/independent generators are the only honest default.

Net effect: the axiom *looked* rigorous (a `Field` instance is a strong,
specific claim) while providing zero actual guarantees about the values the
rest of the code computes with — worse than an honestly-scoped partial
implementation, because it hides the gap instead of documenting it.

## The fix: a real normalizer, no axioms needed

`RatFun` is kept as a friendly surface syntax, but the actual arithmetic
now happens by `normalize : RatFun → PiEField` — evaluating the AST in the
already-sound `PiEField` (a Laurent-monomial ring: canonical form via
sort/merge/drop-zero, the same recipe used throughout `Hyper/`).
`x ≈ y := normalize x = normalize y` becomes the correct equality (same
shape as `Hyper.HyperList.HyperEq`). This makes the border cases that broke
before genuinely true:

```
example : (pi * pi⁻¹ : RatFun) ≈ 1 := by native_decide
example : (pi + e : RatFun) ≈ e + pi := by native_decide
```

The honest remaining limit is now *visible and checkable* rather than
silently wrong: `PiEField.isMonomial` on the normalized form tells you
whether `⁻¹` is trustworthy (exact only for single-term values — the same
scope `R*`'s own `Inv` has). `(π+e)·(π+e)⁻¹ ≈ 1` is provably **false**
through the normalizer, and the file says so directly rather than hiding it
behind an axiom.

`realEval : RatFun → ℝ` (interpreting the AST as actual real numbers,
`piAtom ↦ Real.pi`, `eAtom ↦ Real.exp 1`) — a genuinely good idea from the
earlier version — is kept, but as a plain structural-recursion `def`
instead of an axiom asserting a `RingHom` exists: it's provably correct by
construction, so there was no need to axiomatize it at all.

## The bug found along the way: `Prod`'s order isn't lexicographic

While testing the normalizer, `π + e` and `e + π` initially normalized to
*different* raw term lists — a real bug, not a test artifact. Root cause:
Mathlib's `Prod` order (`ℚ×ℚ ≤`) is componentwise (a partial order — `(0,1)`
and `(1,0)` are simply incomparable under it, confirmed directly:
`decide ((0,1) ≤ (1,0))` and the reverse are both `false`), not
lexicographic. Every multi-exponent `myle` written this session
(`PiEField`, and `Hyper/HyperQuadConstants.lean`, which has the same shape
one level deeper) silently assumed lexicographic tuple order and used it as
the `mergeSort` key — making sort order, and hence `simplify`'s canonical
form, depend on input order. Fixed in both files with an explicit,
fully-recursive `lexLE` comparator; verified `ε+π` and `π+ε` now normalize
identically in `HyperQuadConstants.lean` too. `Hyper/HyperGeneric.lean` and
`Hyper/HyperQuadField.lean` were never at risk — they only ever sort by a
single `ℚ` exponent, which has a genuine total order.

## A claim walked back: "no natural order on π/e coefficients"

When asked whether `GHyper PiEField` could stand in for `HyperList.lean`'s
`𝔽` everywhere, said there's "no principled answer to whether π−e is
positive." That's wrong, and worth recording precisely why, since it
conflates two genuinely different questions:

- **Comparing the actual sizes of two *specific* known transcendentals**
  (`e` vs `π`) is elementary — `e ≈ 2.71828 < π ≈ 3.14159`, provable from
  rational bounds Mathlib already has as theorems
  (`Real.pi_gt_d6`/`pi_lt_d6`, `Real.exp_one_gt_d9`/`exp_one_lt_d9`), not
  axioms. Not open at all.
- **Whether π and e are *algebraically related*** (e.g. does `π² = e³`?) —
  *that's* the genuinely open one, and it's what "no assumed relation"
  in this file's header is actually about.

The `lexLE` comparator built earlier for canonical form doesn't help here
either way — it orders a monomial's *own* exponents for sorting one
expression, not the relative size of two different values.

`PiEField.numericSign` (added after this correction) resolves the
non-conflated question directly: interval arithmetic on rational bounds for
π and e, each checked against the real Mathlib theorems above, decides the
sign of any degree-≤1 combination exactly (`numericSign (eGen - piGen) =
some .lt`, i.e. `e < π`, `native_decide`-checked). It returns `none` — not
a guess — for degree ≥2 (products/powers), which is precisely where the
genuinely open algebraic-independence-adjacent questions live.
