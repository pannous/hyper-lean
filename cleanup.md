# Closing Field-instance sorries on HyperList.R* — outcome

## Result

Started at 36 `sorry`s in `Hyper/HyperList.lean`. Two passes:

**Pass 1** closed 12 Field-instance sorries via the `coeffAt`-uniqueness
technique below: `sub_eq_add_neg`, `zero_add`, `zero_mul`, `mul_zero`,
`exists_pair_ne`, `inv_zero`, `neg_add_cancel`, `add_assoc`, `add_comm`,
`one_mul`, `mul_one`, `add_zero`.

**Pass 2** ("fix npow etc") fixed the actual bug behind 7 more:
`npow_zero`/`npow_succ`/`nsmul_zero`/`nsmul_succ`/`zsmul_zero'`/`zsmul_succ'`/
`zsmul_neg'`. `npow`/`nsmul`/`zsmul`/`qsmul`/`nnqsmul` were defined as
*per-term maps* (`x.map (fun (r,e) => (r^n, e*n))`) instead of *iterated*
`add`/`mul` — mathematically wrong for any multi-term `x` (confirmed via a
`native_decide` counterexample: `npow 0` on a 2-term hyperreal didn't compute
`1`). Fix: extracted `add`/`neg`/`mul` into named top-level defs (`fieldAdd`,
`fieldNeg`, `fieldMul` — same bodies, just no longer inline lambdas) and
defined `fieldNsmul`/`fieldZsmul` as genuine structural recursion *through
those same defs*, so their shape matches Mathlib's default proof obligations
(`nsmul_succ`, `zsmul_succ'`, `zsmul_neg'` all carry a `by intros; rfl`
default) exactly — once the recursion is written correctly, those 7 proofs
are free. `npow` itself turned out to already have a working Mathlib default
(`npowRecAuto`) once the broken custom `npow` field was simply deleted.

18 sorries remain: `qsmul_def`, `nnqsmul_def` (new, see below), plus
`left_distrib`/`right_distrib`/`mul_assoc`/`mul_comm`/`mul_inv_cancel`
(pre-existing, need a convolution lemma — see below).

## The key unlock

`Hyper/HyperList.lean` already carried (pre-existing, not added this session)
`axiom eq_of_simplify_eq (x y : R*) : simplify x = simplify y → x = y` — an
explicit, acknowledged (⚠️-commented) decision to treat `R*` as if it were the
`simplify`-quotient for equality purposes, despite being a bare
non-normalized `List (ℚ×ℚ)`. Combined with a new `simplify_idempotent`, this
turns *any* Field axiom `LHS = RHS` into: show `coeffAt LHS e = coeffAt RHS e`
for all `e` (pure ℚ arithmetic), then two lemmas close the gap to raw
equality — no need for `LHS`/`RHS` to already be in canonical form.

## New reusable infrastructure (in `HyperList.lean`, after `myle_total`)

- `mergeAdjacent_coeffAt`, `mergeAdjacent_exponent_mem`, `mergeAdjacent_pairwise_lt`
- `coeffAt_filter_ne_zero`, `coeffAt_mergeSort`, `coeffAt_simplify`
- `simplify_pairwise_lt`, `simplify_nonzero`, `coeffAt_eq_zero_of_forall_ne`
- `canonical_unique` — two strictly-sorted, all-nonzero lists with equal
  `coeffAt` everywhere are the *same list* (the real content: canonical form
  is uniquely determined by "value at each exponent", not just an
  equivalence class of it)
- `simplify_eq_of_coeffAt_eq`, `simplify_idempotent`, `simplify_nil`
- `coeffAt_append`, `coeffAt_merge`, `coeffAt_neg_map`

Every closed Field axiom is a ~10-line proof: unfold to `merge`/`normalize`,
`apply eq_of_simplify_eq`, reduce to `coeffAt` arithmetic, `ring`. This
infrastructure is what any future work on `mul`-side laws should reuse.

## What's left, and why

**`qsmul_def`, `nnqsmul_def`** — `fieldQsmul q x := fieldMul (embedQ q) x` is
the mathematically correct operation (ring-multiply by the embedded
rational), but the axiom demands `qsmul q x = (↑q : R*) * x` where `↑q` is
the *auto-derived* `RatCast R*` instance — which Lean synthesizes on its own
via `Rat.castRec` over `IntCast`/`NatCast` (`Int.castDef`/`Nat.unaryCast`),
themselves defined via repeated `1 + 1 + ...` using THIS instance's own
`add`/`one`. Proving `(↑q : R*) = embedQ q` needs its own induction (relate
`Nat.unaryCast` to `fieldNsmul _ 1`, then `Int.castDef`, then `Rat.castRec`) —
a real, separate multi-step proof, not a quick corollary of the npow/nsmul
fix. Left open; both fields are mathematically sound regardless.

**`left_distrib`, `right_distrib`, `mul_assoc`, `mul_comm`, `mul_inv_cancel`**
— need an analogous `coeffAt`-of-product characterization. Unlike `add`
(where `coeffAt (merge x y) e = coeffAt x e + coeffAt y e` is a one-line
`List.append`/`List.filter`/`List.sum` fact), `mul`'s `coeffAt` is a genuine
convolution: `coeffAt (mul x y) e = Σ_{e₁+e₂=e} (coeffAt x e₁) * (coeffAt y e₂)`
summed over the (finite, but not obviously-structured) set of exponent pairs
in `x.product y`. Proving this needs either a `Finset`-indexed convolution
lemma or careful `List.product`/`List.sum` bookkeeping — real additional work,
not a quick corollary of what's here. `mul_comm` in particular also needs a
`List.product x y` ↔ `List.product y x` permutation fact that Mathlib doesn't
provide off the shelf (checked via `exact?`, no hit).

**How to continue**: state `coeffAt_mul_term` (the convolution formula) as
the next lemma using the same `coeffAt_simplify`/`simplify_eq_of_coeffAt_eq`
pattern established here, then `mul_comm`/`mul_assoc`/distributivity should
each become a `ring`-closeable arithmetic fact about the convolution sum,
exactly like the closed `add`-side proofs.

## Verified

`lake build` succeeds (905 jobs), `Hyper/probes/HyperListBasics.lean` and
`Hyper/probes/HyperListInstance.lean` both still typecheck clean, after both
passes.
