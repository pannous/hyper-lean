import Hyper.HyperListBridge
/-! Axiom audit for the HyperList bridge.  Run: `lake env lean probes/bridge_axioms.lean`
Expected: bridge theorems use only propext / Classical.choice / Quot.sound,
and the HyperList axiom `eq_of_simplify_eq` is shown inconsistent. -/
open HyperListBridge Hypers

#print axioms toNumber_add
#print axioms toNumber_mul
#print axioms toNumber_eq_iff
#print axioms toNumber_eq_of_decide
#print axioms lt_iff_toNumber_lt
#print axioms le_iff_toNumber_le

/-- `eq_of_simplify_eq` (HyperList.lean) proves `False`: a cancelling list and `[]`
have the same canonical form but are different lists. -/
theorem eq_of_simplify_eq_is_inconsistent : False := by
  have hsame : simplify ([(1, 0), (-1, 0)] : HyperList) = simplify [] :=
    simplify_eq_of_coeffAt_eq fun e => by
      simp only [coeffAt_cons, coeffAt_nil]
      split_ifs <;> norm_num
  exact List.cons_ne_nil _ _ (eq_of_simplify_eq _ _ hsame)

#print axioms eq_of_simplify_eq_is_inconsistent
