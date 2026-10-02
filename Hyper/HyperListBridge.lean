import Hyper.HyperListSemantics
import Hyper.HyperAlgebraic

/-! The executable `HyperList` is a computable subring of `HyperAlgebraic.Number`.

A term `(c, q)` means `c·ω^q`; read at a large real `s` it is `s ↦ c·s^q`.
Rational exponents are fine: `ω^(p/d)` is algebraic, a root of `Y^d - ω^p`.
`toNumber` respects `+ - ·`, identifies exactly the lists with equal
coefficients (`coeffAt`), and turns the list order (`leadSign`, the sign of the
highest-order term) into the order of `Number`. So every `native_decide` fact
about lists is a theorem about the root-closed hyperreals. -/

noncomputable section
namespace HyperListBridge
open Filter HyperAlgebraic HyperListSemantics Hypers

/-! ### Rational-power Laurent expressions as germs -/

/-- `c·ω^q` read at `s`. -/
def termValue (c q : ℚ) (s : ℝ) : ℝ := c * s ^ (q : ℝ)

/-- A list read at `s`: the sum of its terms. -/
def listValue (xs : HyperList) (s : ℝ) : ℝ := (xs.map fun p => termValue p.1 p.2 s).sum

/-- `ω^q` read at `s`. -/
def powerGerm : Multiplicative ℚ →* Germs where
  toFun q := ↑(fun s : ℝ => s ^ ((q.toAdd : ℚ) : ℝ))
  map_one' := congrArg _ (funext fun s => by simp)
  map_mul' a b := by
    rw [← Germ.coe_mul]
    exact Germ.coe_eq.mpr ((eventually_gt_atTop 0).mono fun s hs => by
      simp [Real.rpow_add hs])

def coefficientGerm : ℚ →+* Germs :=
  (Germ.coeRingHom atTop).comp ((Pi.constRingHom ℝ ℝ).comp (Rat.castHom ℝ))

def laurentGerm : Laurent →+* Germs :=
  AddMonoidAlgebra.liftNCRingHom coefficientGerm powerGerm fun _ _ => Commute.all _ _

theorem laurentGerm_single (q c : ℚ) :
    laurentGerm (AddMonoidAlgebra.single q c) = ↑(termValue c q) := by
  change AddMonoidAlgebra.liftNC _ _ _ = _
  rw [AddMonoidAlgebra.liftNC_single]
  rfl

theorem laurentGerm_interpret (xs : HyperList) : laurentGerm (interpret xs) = ↑(listValue xs) := by
  induction xs with
  | nil => simp [interpret]; rfl
  | cons p xs ih =>
    rcases p with ⟨c, q⟩
    rw [interpret, map_add, laurentGerm_single, ih, ← Germ.coe_add]
    congr 1

/-! ### Every term is an algebraic root -/

theorem coe_omega : ((HyperAlgebraic.omega : Number) : Germs) = ↑(fun s : ℝ => s) := by
  rw [HyperAlgebraic.omega, coe_ofBase]
  congr 1
  funext s
  simp [EventualValue.valueAt, AlgebraicHyperreal.omega]

theorem coe_omega_zpow (p : ℤ) :
    ((HyperAlgebraic.omega ^ p : Number) : Germs) = ↑(fun s : ℝ => s ^ p) := by
  cases p with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, zpow_natCast, SubmonoidClass.coe_pow, coe_omega, ← Germ.coe_pow]
    congr 1
  | negSucc n =>
    rw [zpow_negSucc, coe_inv, SubmonoidClass.coe_pow, coe_omega, ← Germ.coe_pow, ← Germ.coe_inv]
    congr 1

theorem termValue_mem (c q : ℚ) : (↑(termValue c q) : Germs) ∈ subring := by
  refine ⟨⟨termValue c q, rfl, (eventually_gt_atTop 0).mono fun s hs =>
    continuousAt_const.mul (Real.continuousAt_rpow_const _ _ (Or.inl hs.ne'))⟩, ?_⟩
  have hpow : (↑(termValue c q) : Germs) ^ q.den =
      ((ofReal ((c : ℝ) ^ q.den) * HyperAlgebraic.omega ^ q.num : Number) : Germs) := by
    rw [← Germ.coe_pow, Subring.coe_mul, coe_omega_zpow]
    change _ = ((ofBase (RatFunc.C _) : Number) : Germs) * _
    rw [coe_const, ← Germ.coe_mul]
    exact Germ.coe_eq.mpr ((eventually_gt_atTop 0).mono fun s hs => by
      simp only [termValue, Pi.pow_apply, Pi.mul_apply, mul_pow]
      rw [← Real.rpow_natCast (s ^ (q : ℝ)), ← Real.rpow_mul hs.le, ← Real.rpow_intCast]
      congr 2
      exact_mod_cast Rat.mul_den_eq_num q)
  exact IsAlgebraic.of_pow q.den_pos (hpow ▸ (mem _).2)

theorem laurentGerm_mem (z : Laurent) : laurentGerm z ∈ subring := by
  induction z using AddMonoidAlgebra.induction_linear with
  | zero => rw [map_zero]; exact subring.zero_mem
  | add a b ha hb => rw [map_add]; exact subring.add_mem ha hb
  | single q c => rw [laurentGerm_single]; exact termValue_mem c q

/-! ### The bridge -/

def toNumber (xs : HyperList) : Number := ⟨laurentGerm (interpret xs), laurentGerm_mem _⟩

theorem coe_toNumber (xs : HyperList) : ((toNumber xs : Number) : Germs) = ↑(listValue xs) :=
  laurentGerm_interpret xs

theorem toNumber_nil : toNumber [] = 0 := Subtype.ext (by simp [toNumber, interpret])

theorem toNumber_congr {x y : HyperList} (h : ∀ e, coeffAt x e = coeffAt y e) :
    toNumber x = toNumber y :=
  Subtype.ext (congrArg laurentGerm ((interpret_eq_iff x y).mpr h))

theorem interpret_merge (x y : HyperList) : interpret (x + y) = interpret x + interpret y := by
  have h (e : ℚ) : coeffAt (x + y) e = coeffAt x e + coeffAt y e := coeffAt_merge x y e
  ext e
  simpa using h e

theorem interpret_negate (x : HyperList) : interpret (-x) = -interpret x := by
  have h (e : ℚ) : coeffAt (-x) e = -coeffAt x e := coeffAt_neg_map x e
  ext e
  simpa using h e

theorem toNumber_add (x y : HyperList) : toNumber (x + y) = toNumber x + toNumber y :=
  Subtype.ext (by simp only [toNumber, interpret_merge, map_add]; rfl)

theorem toNumber_neg (x : HyperList) : toNumber (-x) = -toNumber x :=
  Subtype.ext (by simp only [toNumber, interpret_negate, map_neg]; rfl)

theorem toNumber_sub (x y : HyperList) : toNumber (x - y) = toNumber x - toNumber y := by
  change toNumber (x + -y) = _
  rw [toNumber_add, toNumber_neg, sub_eq_add_neg]

theorem toNumber_mul (x y : HyperList) : toNumber (x * y) = toNumber x * toNumber y :=
  Subtype.ext (by
    change laurentGerm (interpret (fieldMul x y)) = _
    simp only [interpret_mul, map_mul]; rfl)

theorem toNumber_simplify (x : HyperList) : toNumber (simplify x) = toNumber x :=
  toNumber_congr (coeffAt_simplify x)

/-! ### The leading term decides the sign -/

theorem listValue_cons_factor (r e : ℚ) (rest : HyperList) {s : ℝ} (hs : 0 < s) :
    listValue ((r, e) :: rest) s =
      s ^ (e : ℝ) * (r + (rest.map fun p => (p.1 : ℝ) * s ^ ((p.2 : ℝ) - e)).sum) := by
  simp only [listValue, termValue, List.map_cons, List.sum_cons, mul_add, ← List.sum_map_mul_left]
  congr 1
  · ring
  · congr 1
    refine List.map_congr_left fun p _ => ?_
    rw [mul_left_comm, ← Real.rpow_add hs, add_sub_cancel]

theorem sign_ratCast (r : ℚ) : SignType.sign (r : ℝ) = SignType.sign r := by
  rcases lt_trichotomy r 0 with h | h | h
  · rw [sign_neg h, sign_neg (by exact_mod_cast h)]
  · simp [h]
  · rw [sign_pos h, sign_pos (by exact_mod_cast h)]

theorem eventually_sign_listValue {r e : ℚ} {rest : HyperList} (hr : r ≠ 0)
    (hlower : ∀ p, List.Mem p rest → p.2 < e) :
    ∀ᶠ s in atTop, SignType.sign (listValue ((r, e) :: rest) s) = SignType.sign r := by
  have hlimit : Tendsto (fun s : ℝ => (r : ℝ) + (rest.map fun p => (p.1 : ℝ) *
      s ^ ((p.2 : ℝ) - e)).sum) atTop (nhds (r : ℝ)) := by
    have hterms := tendsto_list_sum (l := rest) (x := atTop)
      (f := fun p (s : ℝ) => (p.1 : ℝ) * s ^ ((p.2 : ℝ) - e)) (a := fun _ => 0) fun p hp => by
        have hneg : 0 < (e : ℝ) - p.2 := by exact_mod_cast sub_pos.mpr (hlower p hp)
        simpa [neg_sub] using (tendsto_rpow_neg_atTop hneg).const_mul (p.1 : ℝ)
    simpa using tendsto_const_nhds.add hterms
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr
  have hinner : ∀ᶠ s in atTop, SignType.sign ((r : ℝ) + (rest.map fun p => (p.1 : ℝ) *
      s ^ ((p.2 : ℝ) - e)).sum) = SignType.sign (r : ℝ) := by
    rcases lt_or_gt_of_ne hr' with hneg | hpos
    · filter_upwards [hlimit.eventually (eventually_lt_nhds hneg)] with s hs
      rw [sign_neg hs, sign_neg hneg]
    · filter_upwards [hlimit.eventually (eventually_gt_nhds hpos)] with s hs
      rw [sign_pos hs, sign_pos hpos]
  filter_upwards [hinner, eventually_gt_atTop 0] with s hs hpos
  rw [listValue_cons_factor r e rest hpos, sign_mul, hs, sign_pos (Real.rpow_pos_of_pos hpos _),
    one_mul, sign_ratCast]

/-- `leadSign` (sign of the highest-order term of the canonical form) is the sign in `Number`. -/
theorem leadSign_cases (x : HyperList) :
    (leadSign x = .eq ∧ toNumber x = 0) ∨ (leadSign x = .lt ∧ toNumber x < 0) ∨
      (leadSign x = .gt ∧ 0 < toNumber x) := by
  rw [← toNumber_simplify]
  unfold leadSign
  have hsorted := simplify_pairwise_lt x
  have hnonzero := simplify_nonzero x
  generalize simplify x = l at hsorted hnonzero ⊢
  cases l with
  | nil => exact Or.inl ⟨rfl, toNumber_nil⟩
  | cons p rest =>
    rcases p with ⟨r, e⟩
    have hr : r ≠ 0 := hnonzero (r, e) (List.Mem.head _)
    have hsign := eventually_sign_listValue hr fun q hq => (List.pairwise_cons.mp hsorted).1 q hq
    have hcompare :=
      lt_iff_eventually (coe_toNumber ((r, e) :: rest)).symm (g := 0) (y := 0) rfl
    have hcompare' :=
      lt_iff_eventually (f := 0) (x := 0) rfl (coe_toNumber ((r, e) :: rest)).symm
    rcases lt_or_gt_of_ne hr with hneg | hpos
    · refine Or.inr (Or.inl ⟨by simp [not_lt.mpr hneg.le], hcompare.mpr ?_⟩)
      exact hsign.mono fun s hs => sign_eq_neg_one_iff.mp (by rw [hs, sign_neg hneg])
    · refine Or.inr (Or.inr ⟨by simp [hpos], hcompare'.mpr ?_⟩)
      exact hsign.mono fun s hs => sign_eq_one_iff.mp (by rw [hs, sign_pos hpos])

theorem toNumber_lt_zero_iff (x : HyperList) : toNumber x < 0 ↔ leadSign x = .lt := by
  rcases leadSign_cases x with ⟨h, hx⟩ | ⟨h, hx⟩ | ⟨h, hx⟩
  · simp [h, hx]
  · simp [h, hx]
  · simp [h, hx.le.not_gt]

theorem toNumber_pos_iff (x : HyperList) : 0 < toNumber x ↔ leadSign x = .gt := by
  rcases leadSign_cases x with ⟨h, hx⟩ | ⟨h, hx⟩ | ⟨h, hx⟩
  · simp [h, hx]
  · simp [h, hx.le.not_gt]
  · simp [h, hx]

theorem toNumber_nonneg_iff (x : HyperList) : 0 ≤ toNumber x ↔ leadSign x ≠ .lt := by
  rw [← not_lt, toNumber_lt_zero_iff]

theorem toNumber_eq_zero_iff (x : HyperList) : toNumber x = 0 ↔ leadSign x = .eq := by
  rcases leadSign_cases x with ⟨h, hx⟩ | ⟨h, hx⟩ | ⟨h, hx⟩
  · simp [h, hx]
  · simp [h, hx.ne]
  · simp [h, hx.ne']

/-! ### Main theorems: the list order and equality are the order and equality of `Number` -/

theorem lt_iff_toNumber_lt (x y : HyperList) : x < y ↔ toNumber x < toNumber y := by
  change leadSign (x - y) = Ordering.lt ↔ _
  rw [← toNumber_lt_zero_iff, toNumber_sub, sub_neg]

theorem le_iff_toNumber_le (x y : HyperList) : x ≤ y ↔ toNumber x ≤ toNumber y := by
  change leadSign (x - y) ≠ Ordering.gt ↔ _
  rw [Ne, ← toNumber_pos_iff, toNumber_sub, sub_pos, not_lt]

theorem toNumber_eq_iff (x y : HyperList) :
    toNumber x = toNumber y ↔ ∀ e, coeffAt x e = coeffAt y e := by
  refine ⟨fun h e => ?_, toNumber_congr⟩
  have hsign : leadSign (x - y) = .eq := by
    rw [← toNumber_eq_zero_iff, toNumber_sub, h, sub_self]
  have hnil : simplify (x - y) = [] := by
    unfold leadSign at hsign
    split at hsign
    · assumption
    · split_ifs at hsign
  have hdiff : coeffAt (x - y) e = coeffAt x e - coeffAt y e := by
    have hmerge : coeffAt (x - y) e = coeffAt x e + coeffAt (-y) e := coeffAt_merge x (-y) e
    have hneg : coeffAt (-y) e = -coeffAt y e := coeffAt_neg_map y e
    rw [hmerge, hneg, ← sub_eq_add_neg]
  have hzero := coeffAt_simplify (x - y) e
  rw [hnil, coeffAt_nil, hdiff] at hzero
  exact sub_eq_zero.mp hzero.symm

/-- Two lists denote the same hyperreal iff their canonical forms agree: decidable. -/
theorem toNumber_eq_iff_simplify_eq (x y : HyperList) :
    toNumber x = toNumber y ↔ simplify x = simplify y := by
  rw [toNumber_eq_iff]
  refine ⟨simplify_eq_of_coeffAt_eq, fun h e => ?_⟩
  rw [← coeffAt_simplify x, h, coeffAt_simplify]

/-- Decide semantic equality by comparing canonical forms with `List`'s own `DecidableEq`.
Deliberately not the `DecidableEq R*` instance of `HyperList.lean`, which rests on the
unsound axiom `eq_of_simplify_eq`. Use as `toNumber_eq_of_decide _ _ (by native_decide)`. -/
theorem toNumber_eq_of_decide (x y : HyperList)
    (h : @decide (simplify x = simplify y) (instDecidableEqList (simplify x) (simplify y)) = true) :
    toNumber x = toNumber y :=
  (toNumber_eq_iff_simplify_eq x y).mpr (@of_decide_eq_true _ (instDecidableEqList _ _) h)

end HyperListBridge
