# Closing Field-instance sorries on HyperList.R* — outcome

## Result

Started at 36 `sorry`s in `Hyper/HyperList.lean` (24 in the `Field R*` instance,
12 in helper `smul`/`zsmul` lemmas above it). Closed 12 Field-instance sorries:
`sub_eq_add_neg`, `zero_add`, `zero_mul`, `mul_zero`, `exists_pair_ne`,
`inv_zero`, `neg_add_cancel`, `add_assoc`, `add_comm`, `one_mul`, `mul_one`,
`add_zero`. 24 remain — see below for exactly why each is or isn't closable
without further, separately-scoped work.

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

**`zsmul_succ'`, `zsmul_neg'`, `nsmul_zero`, `nsmul_succ`, `npow_zero`,
`npow_succ`, `nnqsmul_def`, `qsmul_def`** — not a proof gap, a *definition*
gap. `npow := fun n x => x.map (fun (r,e) => (r^n, e*n))` is per-term
exponentiation, not iterated multiplication — mathematically wrong for any
`x` with more than one term (e.g. `npow 0 [(1,0),(1,1)]` should be `1` but
computes `[(1,0),(1,0)]`, which doesn't even `simplify`-equal `1`). Verified
this is a real counterexample, not a proof-technique gap, via `native_decide`.
Same issue for `nsmul`/`zsmul`/`qsmul`/`nnqsmul` (all per-term maps instead of
repeated `add`). Closing these needs redefining the operations themselves
(e.g. via `npowRec`/Mathlib defaults, or proper recursion) — a distinct,
riskier change than adding proofs, left for a separate pass.

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
`Hyper/probes/HyperListInstance.lean` both still typecheck clean.
