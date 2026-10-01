# Porting hyper from Lean/mathlib v4.27.0 to v4.34.1 (2026-10-01)

Context: the shared Lake packages dir (`../notes/shared-lake.md`) forced the upgrade.
`lake build` (all `Hyper.+`) and `./test.sh` pass.

## Root cause of ~90% of the errors: `def HyperList`
In v4.34, instance synthesis checks the types of metavariable assignments at
`instances` transparency. A plain `def HyperList := List (𝔽 × ℰ)` no longer unifies with
`List` there. As a result `x = []` became undecidable, `merge` became `sorry`, and that cascaded
into the rw/split_ifs/native_decide failures.

Fix: `@[instance_reducible] def HyperList`. Do **not** use `abbrev`/`@[reducible]`:
- reducible defs unfold when computing discrimination-tree keys, so R* and List instances merge.
- The axiom-backed `DecidableEq R*` (via `eq_of_simplify_eq`, declared later) then overrides
  raw list equality everywhere. `raw_lists_differ` in test_hyperlist_foundation fails, and
  `++` on lists becomes `merge` (`HAppend R* R* R*`).
`instance_reducible` unfolds at instances transparency but keeps the keys distinct, which matches
the v4.27 behaviour.

## Smaller API / behaviour changes
- `show simplify (a ++ b)`: write `List.append a b`, matching `merge`'s body. `++` can now
  resolve to the R* `HAppend` (merge).
- Mathlib removed `Transitive`. `instance : Reflexive/Symmetric/Equivalence ...` on a non-class
  is now an error. These became theorems `hyperEq_reflexive/symmetric/equivalence` plus
  `instance : IsTrans R* HyperEq`.
- `AddMonoidAlgebra` is now a structure with `.coeff : M →₀ R`. It is no longer a coercible Finsupp.
  `x e` became `x.coeff e`, `single_apply` became `coeff_single` + `Finsupp.single_apply`, and
  `neg_apply` became `coeff_neg` + `Finsupp.neg_apply`.
- `RingCone` carrier membership no longer unfolds in `simpa`. Add `Set.mem_setOf_eq`.
- `simpa only [lemma]` no longer unfolds a `def Approx` to its body. Add `Approx` to the simp set.
- `simp` now closes some goals that used to need a trailing `rfl`, so that `rfl` fails with "No goals".
- simp no longer reduces `(NonzeroCount.mk ⟨c,o⟩ h).value`. Added the
  `@[simp] NonzeroCount.value_mk` lemma.
- Many `if_pos/if_neg/if_true` deprecation warnings (use `ite_eq_left` etc.). They are harmless and were left as is.

## Test change (user-approved)
The trailing `rfl` in test_hyperlist_foundation.lean `disk_point_lists_value` was deleted: simp now
closes the goal itself. `./test.sh` passes, including both axiom audits.
