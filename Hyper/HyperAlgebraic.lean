import Hyper.EventualValue
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Order.Filter.Germ.OrderedMonoid

/-! Hyperreals with roots: ℝ(ω) extended by every algebraic root, symbolically.

An element is a germ at `s → +∞` (read ω as a large real `s`) that is
* eventually continuous, and
* algebraic over ℝ(ω): it solves `P(ω, y) = 0` for some nonzero polynomial `P`.

So `√(1+ω)` is not a series but the germ `s ↦ √(1+s)`, pinned down by its
defining equation `y² - (1+ω) = 0`. No ultrafilter, no Hahn series, no limits.

Key fact (`eventually_sign_eq`): such a germ has an eventually constant sign.
A zero of `y` at large `s` must be an isolated-free zero, because the factor
`P(s, 0) ≠ 0` stays nonzero nearby; connectedness of `(s₁, ∞)` does the rest.
This makes the germs a linearly ordered field (`HyperAlgebraic`) in which
every nonnegative element has every `n`-th root and every element has odd roots. -/

noncomputable section
namespace HyperAlgebraic
open Polynomial Filter Topology EventualValue

abbrev Germs := Germ (atTop : Filter ℝ) ℝ
abbrev Base := RatFunc ℝ

instance : Algebra Base Germs := toGerm.toAlgebra

theorem algebraMap_eq (x : Base) : algebraMap Base Germs x = ↑(valueAt x) := rfl

/-! ### Pointwise reading of polynomial equations -/

/-- `p(s, y)`: the coefficients of `p` read at `s`, evaluated at `y`. -/
def evalAt (p : Base[X]) (s y : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (p.natDegree + 1), valueAt (p.coeff i) s * y ^ i

theorem aeval_coe (p : Base[X]) (f : ℝ → ℝ) :
    aeval (f : Germs) p = ↑(fun s => evalAt p s (f s)) := by
  have hfun : (fun s => evalAt p s (f s)) =
      ∑ i ∈ Finset.range (p.natDegree + 1), valueAt (p.coeff i) * f ^ i := by
    funext s
    simp [evalAt, Finset.sum_apply]
  rw [aeval_eq_sum_range, hfun]
  change _ = Germ.coeRingHom atTop _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, algebraMap_eq, map_mul, map_pow]
  rfl

theorem evalAt_zero (p : Base[X]) (s : ℝ) : evalAt p s 0 = valueAt (p.coeff 0) s := by
  simp [evalAt, Finset.sum_range_succ']

theorem eventually_continuousAt_evalAt (p : Base[X]) {f : ℝ → ℝ}
    (hf : ∀ᶠ s in atTop, ContinuousAt f s) :
    ∀ᶠ s in atTop, ContinuousAt (fun t => evalAt p t (f t)) s := by
  have hcoeff : ∀ᶠ s in atTop, ∀ i ∈ Finset.range (p.natDegree + 1),
      ContinuousAt (valueAt (p.coeff i)) s :=
    (Finset.eventually_all _).mpr fun i _ => eventually_continuousAt_valueAt _
  filter_upwards [hf, hcoeff] with s hfs hcs
  unfold evalAt
  exact tendsto_finsetSum _ fun i hi => (hcs i hi).mul (hfs.pow i)

/-! ### Eventual sign of continuous algebraic germs -/

def EventuallyContinuous (f : ℝ → ℝ) : Prop := ∀ᶠ s in atTop, ContinuousAt f s

/-- A continuous algebraic germ never oscillates: its sign is eventually constant. -/
theorem eventually_sign_eq {f : ℝ → ℝ} (hcont : EventuallyContinuous f)
    (halg : IsAlgebraic Base (f : Germs)) :
    ∃ σ : SignType, ∀ᶠ s in atTop, SignType.sign (f s) = σ := by
  obtain ⟨p, hp, hroot⟩ := halg
  obtain ⟨q, hpq, hq⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp 0
  have hq0 : q.coeff 0 ≠ 0 := by
    intro h0; exact hq (by simpa using X_dvd_iff.mpr h0)
  have hfactor : ∀ᶠ s in atTop, f s ^ rootMultiplicity 0 p * evalAt q s (f s) = 0 := by
    rw [hpq, map_mul, map_pow] at hroot
    simp only [map_zero, sub_zero, aeval_X, aeval_coe, ← Germ.coe_pow, ← Germ.coe_mul] at hroot
    exact Germ.coe_eq.mp hroot
  obtain ⟨s₁, hs₁⟩ := eventually_atTop.mp (((hcont.and hfactor).and
    (eventually_continuousAt_evalAt q hcont)).and (eventually_valueAt_ne_zero hq0))
  have locallySigned : ∀ x > s₁, ∀ᶠ t in 𝓝 x, SignType.sign (f t) = SignType.sign (f x) := by
    intro x hx
    obtain ⟨⟨⟨hfx, -⟩, hevalx⟩, hq0x⟩ := hs₁ x hx.le
    rcases lt_trichotomy (f x) 0 with hneg | hzero | hpos
    · filter_upwards [hfx.eventually (eventually_lt_nhds hneg)] with t ht
      rw [sign_neg ht, sign_neg hneg]
    · have hne : evalAt q x (f x) ≠ 0 := by rwa [hzero, evalAt_zero]
      filter_upwards [hevalx.eventually_ne hne, Ioi_mem_nhds hx] with t ht hts
      have hft := (hs₁ t (le_of_lt hts)).1.1.2
      rw [eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hft).resolve_right ht), hzero]
    · filter_upwards [hfx.eventually (eventually_gt_nhds hpos)] with t ht
      rw [sign_pos ht, sign_pos hpos]
  have : PreconnectedSpace (Set.Ioi s₁) := Subtype.preconnectedSpace isPreconnected_Ioi
  have hlc : IsLocallyConstant (fun x : Set.Ioi s₁ => SignType.sign (f x)) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    rw [nhds_subtype_eq_comap]
    exact (locallySigned x x.2).comap _
  refine ⟨SignType.sign (f (s₁ + 1)), ?_⟩
  filter_upwards [eventually_gt_atTop s₁] with s hs
  exact hlc.apply_eq_of_preconnectedSpace ⟨s, hs⟩ ⟨s₁ + 1, by simp⟩

/-! ### The field `Number` -/

def IsHyperAlgebraic (g : Germs) : Prop :=
  (∃ f : ℝ → ℝ, (f : Germs) = g ∧ EventuallyContinuous f) ∧ IsAlgebraic Base g

theorem EventuallyContinuous.of_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    EventuallyContinuous f :=
  Eventually.of_forall fun _ => hf.continuousAt

/-- Any representative of a member has an eventual sign. -/
theorem eventually_sign_of_mem {g : Germs} (hg : IsHyperAlgebraic g) {f : ℝ → ℝ}
    (hf : (f : Germs) = g) : ∃ σ : SignType, ∀ᶠ s in atTop, SignType.sign (f s) = σ := by
  obtain ⟨⟨f₀, hf₀, hc⟩, halg⟩ := hg
  obtain ⟨σ, hσ⟩ := eventually_sign_eq hc (by rw [hf₀]; exact halg)
  refine ⟨σ, ?_⟩
  filter_upwards [hσ, Germ.coe_eq.mp (hf₀.trans hf.symm)] with s hs heq
  rw [← heq, hs]

def subring : Subring Germs where
  carrier := {g | IsHyperAlgebraic g}
  zero_mem' := ⟨⟨0, rfl, .of_continuous continuous_const⟩, isAlgebraic_zero⟩
  one_mem' := ⟨⟨1, rfl, .of_continuous continuous_const⟩, isAlgebraic_one⟩
  add_mem' := by
    rintro _ _ ⟨⟨f, rfl, hf⟩, ha⟩ ⟨⟨g, rfl, hg⟩, hb⟩
    exact ⟨⟨f + g, rfl, (hf.and hg).mono fun _ h => h.1.add h.2⟩, ha.add hb⟩
  mul_mem' := by
    rintro _ _ ⟨⟨f, rfl, hf⟩, ha⟩ ⟨⟨g, rfl, hg⟩, hb⟩
    exact ⟨⟨f * g, rfl, (hf.and hg).mono fun _ h => h.1.mul h.2⟩, ha.mul hb⟩
  neg_mem' := by
    rintro _ ⟨⟨f, rfl, hf⟩, ha⟩
    exact ⟨⟨-f, rfl, hf.mono fun _ h => h.neg⟩, ha.neg⟩

/-- Hyperreals closed under algebraic roots. -/
abbrev Number := ↥subring

theorem mem (x : Number) : IsHyperAlgebraic (x : Germs) := x.2

theorem eventually_ne_zero_of_ne_zero {x : Number} (hx : x ≠ 0) {f : ℝ → ℝ}
    (hf : (f : Germs) = x) : ∀ᶠ s in atTop, f s ≠ 0 := by
  obtain ⟨σ, hσ⟩ := eventually_sign_of_mem (mem x) hf
  by_cases hσ0 : σ = 0
  · subst hσ0
    exfalso
    apply hx
    apply Subtype.ext
    rw [← hf]
    exact Germ.coe_eq.mpr (hσ.mono fun s hs => sign_eq_zero_iff.mp hs)
  · filter_upwards [hσ] with s hs h
    exact hσ0 (by rw [← hs, h, sign_zero])

theorem inv_mem (x : Number) : (x : Germs)⁻¹ ∈ subring := by
  obtain ⟨⟨f, hf, hc⟩, halg⟩ := mem x
  by_cases hx : x = 0
  · subst hx
    rw [← hf, ← Germ.coe_inv]
    have hf0 : (f : Germs) = ((0 : ℝ → ℝ) : Germs) := hf
    have hev := Germ.coe_eq.mp hf0
    have : ((f⁻¹ : ℝ → ℝ) : Germs) = ((0 : ℝ → ℝ) : Germs) :=
      Germ.coe_eq.mpr (hev.mono fun s hs => by simp [hs])
    rw [this]
    exact subring.zero_mem
  have hne := eventually_ne_zero_of_ne_zero hx hf
  have hmul : (x : Germs) * (x : Germs)⁻¹ = 1 := by
    rw [← hf, ← Germ.coe_inv, ← Germ.coe_mul]
    exact Germ.coe_eq.mpr (hne.mono fun s hs => mul_inv_cancel₀ hs)
  refine ⟨⟨f⁻¹, by rw [Germ.coe_inv, hf], (hc.and hne).mono fun _ h => h.1.inv₀ h.2⟩, ?_⟩
  let _ : Invertible (x : Germs) := ⟨_, (mul_comm _ _).trans hmul, hmul⟩
  exact halg.invOf

instance : Inv Number := ⟨fun x => ⟨(x : Germs)⁻¹, inv_mem x⟩⟩

@[simp] theorem coe_inv (x : Number) : ((x⁻¹ : Number) : Germs) = (x : Germs)⁻¹ := rfl

instance : Field Number where
  __ := (inferInstance : CommRing Number)
  inv := Inv.inv
  mul_inv_cancel x hx := by
    obtain ⟨⟨f, hf, -⟩, -⟩ := mem x
    apply Subtype.ext
    change (x : Germs) * (x : Germs)⁻¹ = 1
    rw [← hf, ← Germ.coe_inv, ← Germ.coe_mul]
    exact Germ.coe_eq.mpr ((eventually_ne_zero_of_ne_zero hx hf).mono
      fun s hs => mul_inv_cancel₀ hs)
  inv_zero := by
    apply Subtype.ext
    change ((0 : ℝ → ℝ) : Germs)⁻¹ = ((0 : ℝ → ℝ) : Germs)
    rw [← Germ.coe_inv]
    exact congrArg _ (funext fun _ => inv_zero (G₀ := ℝ))
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

/-! ### The order: eventual comparison (inherited from germs), total by `eventually_sign_eq` -/

theorem exists_rep (x : Number) : ∃ f : ℝ → ℝ, (f : Germs) = x :=
  let ⟨⟨f, hf, _⟩, _⟩ := mem x
  ⟨f, hf⟩

/-- A chosen representative: `x` read as a real function of `s`. -/
def rep (x : Number) : ℝ → ℝ := (exists_rep x).choose

theorem coe_rep (x : Number) : (rep x : Germs) = x := (exists_rep x).choose_spec

/-- Comparison is eventual comparison of any representatives. -/
theorem le_iff_eventually {x y : Number} {f g : ℝ → ℝ} (hf : (f : Germs) = x)
    (hg : (g : Germs) = y) : x ≤ y ↔ ∀ᶠ s in atTop, f s ≤ g s := by
  change (x : Germs) ≤ y ↔ _
  rw [← hf, ← hg]
  exact Germ.coe_le

theorem coe_sub_rep {x y : Number} {f g : ℝ → ℝ} (hf : (f : Germs) = x)
    (hg : (g : Germs) = y) : ((f - g : ℝ → ℝ) : Germs) = ((x - y : Number) : Germs) := by
  rw [Germ.coe_sub, hf, hg]; rfl

instance : LinearOrder Number :=
  { (inferInstance : PartialOrder Number) with
    le_total x y := by
      obtain ⟨f, hf⟩ := exists_rep x
      obtain ⟨g, hg⟩ := exists_rep y
      obtain ⟨σ, hσ⟩ := eventually_sign_of_mem (mem (x - y)) (coe_sub_rep hf hg)
      rw [le_iff_eventually hf hg, le_iff_eventually hg hf]
      rcases σ with _ | _ | _
      · exact Or.inl (hσ.mono fun _ hs => sub_nonpos.mp (sign_eq_zero_iff.mp hs).le)
      · exact Or.inl (hσ.mono fun _ hs => sub_nonpos.mp (sign_eq_neg_one_iff.mp hs).le)
      · exact Or.inr (hσ.mono fun _ hs => sub_nonneg.mp (sign_eq_one_iff.mp hs).le)
    toDecidableLE := Classical.decRel _ }

instance : IsOrderedAddMonoid Number where
  add_le_add_left _ _ hab _ := add_le_add (α := Germs) hab le_rfl

instance : ZeroLEOneClass Number where
  zero_le_one := (le_iff_eventually (f := 0) (g := 1) rfl rfl).mpr
    (Eventually.of_forall fun _ => zero_le_one)

instance : IsOrderedRing Number :=
  .of_mul_nonneg fun a b ha hb => by
    obtain ⟨f, hf⟩ := exists_rep a
    obtain ⟨g, hg⟩ := exists_rep b
    have hfg : ((f * g : ℝ → ℝ) : Germs) = ((a * b : Number) : Germs) := by
      rw [Germ.coe_mul, hf, hg]; rfl
    rw [le_iff_eventually (f := 0) rfl hf] at ha
    rw [le_iff_eventually (f := 0) rfl hg] at hb
    exact (le_iff_eventually (f := 0) rfl hfg).mpr
      ((ha.and hb).mono fun _ h => mul_nonneg h.1 h.2)

theorem eventually_ne_of_ne {x y : Number} (hxy : x ≠ y) {f g : ℝ → ℝ}
    (hf : (f : Germs) = x) (hg : (g : Germs) = y) : ∀ᶠ s in atTop, f s ≠ g s := by
  filter_upwards [eventually_ne_zero_of_ne_zero (sub_ne_zero.mpr hxy) (coe_sub_rep hf hg)]
    with s hs
  exact sub_ne_zero.mp hs

theorem lt_iff_eventually {x y : Number} {f g : ℝ → ℝ} (hf : (f : Germs) = x)
    (hg : (g : Germs) = y) : x < y ↔ ∀ᶠ s in atTop, f s < g s := by
  constructor
  · intro hxy
    filter_upwards [(le_iff_eventually hf hg).mp hxy.le, eventually_ne_of_ne hxy.ne hf hg]
      with s hle hne using lt_of_le_of_ne hle hne
  · intro hlt
    refine lt_of_le_of_ne ((le_iff_eventually hf hg).mpr (hlt.mono fun _ h => h.le)) ?_
    rintro rfl
    obtain ⟨s, hs, heq⟩ := (hlt.and (Germ.coe_eq.mp (hf.trans hg.symm))).exists
    exact hs.ne heq

/-! ### ℝ(ω) inside `Number` -/

def ofBase : Base →+* Number :=
  toGerm.codRestrict subring fun x =>
    ⟨⟨valueAt x, rfl, eventually_continuousAt_valueAt x⟩, isAlgebraic_algebraMap x⟩

@[simp] theorem coe_ofBase (x : Base) : ((ofBase x : Number) : Germs) = ↑(valueAt x) := rfl

open scoped AlgebraicHyperreal in
theorem ofBase_lt_ofBase {x y : Base} (hxy : x < y) : ofBase x < ofBase y :=
  (lt_iff_eventually (coe_ofBase x).symm (coe_ofBase y).symm).mpr (eventually_valueAt_lt hxy)

def ofReal (r : ℝ) : Number := ofBase (RatFunc.C r)

def omega : Number := ofBase AlgebraicHyperreal.omega
def epsilon : Number := ofBase AlgebraicHyperreal.epsilon

theorem coe_const (r : ℝ) : ((ofBase (RatFunc.C r) : Number) : Germs) = ↑(fun _ : ℝ => r) :=
  congrArg _ (funext (valueAt_const r))

/-! ### Roots -/

/-- Applying a continuous `ψ` that is linear on each sign class keeps us in `Number`. -/
theorem map_mem_of_signwise_linear {ψ : ℝ → ℝ} (c : SignType → ℝ)
    (hc : ∀ r, ψ r = c (SignType.sign r) * r) (x : Number) :
    Germ.map ψ (x : Germs) ∈ subring := by
  obtain ⟨⟨f, hf, hcont⟩, -⟩ := mem x
  obtain ⟨σ, hσ⟩ := eventually_sign_of_mem (mem x) hf
  have hlin : Germ.map ψ (x : Germs) = ((ofBase (RatFunc.C (c σ)) * x : Number) : Germs) := by
    change _ = ((ofBase (RatFunc.C (c σ)) : Number) : Germs) * (x : Germs)
    rw [← hf, Germ.map_coe, coe_const, ← Germ.coe_mul]
    exact Germ.coe_eq.mpr (hσ.mono fun s hs => by simp [hc, hs])
  rw [hlin]
  exact (ofBase (RatFunc.C (c σ)) * x).2

/-- A continuous `φ` whose `n`-th power is signwise linear: `φ(x)` is an algebraic root. -/
theorem map_mem_of_pow {φ ψ : ℝ → ℝ} (hφ : Continuous φ) {n : ℕ}
    (hn : n ≠ 0) (c : SignType → ℝ) (hc : ∀ r, ψ r = c (SignType.sign r) * r)
    (hpow : ∀ r, φ r ^ n = ψ r) (x : Number) : Germ.map φ (x : Germs) ∈ subring := by
  obtain ⟨⟨f, hf, hcont⟩, -⟩ := mem x
  refine ⟨⟨φ ∘ f, by rw [← hf, Germ.map_coe],
    hcont.mono fun _ h => hφ.continuousAt.comp h⟩, ?_⟩
  have hpowGerm : Germ.map φ (x : Germs) ^ n = Germ.map ψ (x : Germs) := by
    rw [← hf, Germ.map_coe, Germ.map_coe, ← Germ.coe_pow]
    exact congrArg _ (funext fun s => hpow (f s))
  exact IsAlgebraic.of_pow (Nat.pos_of_ne_zero hn)
    (hpowGerm ▸ (map_mem_of_signwise_linear c hc x).2)

theorem abs_eq_sign_mul (r : ℝ) : |r| = (SignType.sign r : ℝ) * r := by
  rcases lt_trichotomy r 0 with h | h | h
  · simp [abs_of_neg h, sign_neg h]
  · simp [h]
  · simp [abs_of_pos h, sign_pos h]

theorem max_zero_eq_sign_mul (r : ℝ) :
    max r 0 = (if SignType.sign r = 1 then 1 else 0) * r := by
  rcases lt_trichotomy r 0 with h | h | h
  · simp [max_eq_right h.le, sign_neg h]
  · simp [h]
  · simp [max_eq_left h.le, sign_pos h]

/-- `n`-th root of `|x|`, pointwise `s ↦ |x(s)|^(1/n)`. -/
def nthRoot (n : ℕ) (hn : n ≠ 0) (x : Number) : Number :=
  ⟨Germ.map (fun r => |r| ^ (n⁻¹ : ℝ)) x,
    map_mem_of_pow ((Real.continuous_rpow_const (by positivity)).comp continuous_abs) hn (fun σ => (σ : ℝ)) abs_eq_sign_mul
      (fun r => Real.rpow_inv_natCast_pow (abs_nonneg r) hn) x⟩

/-- `√x`, pointwise `Real.sqrt` (so `√x = 0` for `x < 0`, exactly as in ℝ). -/
def sqrt (x : Number) : Number :=
  ⟨Germ.map Real.sqrt x,
    map_mem_of_pow Real.continuous_sqrt two_ne_zero
      (fun σ => if σ = 1 then 1 else 0) max_zero_eq_sign_mul
      (fun r => by
        rcases le_total 0 r with h | h
        · simp [Real.sq_sqrt h, h]
        · simp [Real.sqrt_eq_zero'.mpr h, h]) x⟩

theorem coe_sqrt (x : Number) : ((sqrt x : Number) : Germs) = Germ.map Real.sqrt x := rfl

theorem sqrt_nonneg (x : Number) : 0 ≤ sqrt x := by
  obtain ⟨f, hf⟩ := exists_rep x
  have hroot : ((sqrt x : Number) : Germs) = ↑(fun s => Real.sqrt (f s)) := by
    rw [coe_sqrt, ← hf, Germ.map_coe]; rfl
  exact (le_iff_eventually (f := 0) rfl hroot.symm).mpr
    (Eventually.of_forall fun s => Real.sqrt_nonneg _)

theorem nthRoot_nonneg (n : ℕ) (hn : n ≠ 0) (x : Number) : 0 ≤ nthRoot n hn x := by
  obtain ⟨⟨f, hf, -⟩, -⟩ := mem x
  have hroot : ((nthRoot n hn x : Number) : Germs) = ↑(fun s => |f s| ^ (n⁻¹ : ℝ)) := by
    change Germ.map _ (x : Germs) = _
    rw [← hf, Germ.map_coe]; rfl
  exact (le_iff_eventually (f := 0) rfl hroot.symm).mpr
    (Eventually.of_forall fun s => Real.rpow_nonneg (abs_nonneg _) _)

theorem nthRoot_pow (n : ℕ) (hn : n ≠ 0) {x : Number} (hx : 0 ≤ x) :
    nthRoot n hn x ^ n = x := by
  obtain ⟨⟨f, hf, -⟩, -⟩ := mem x
  have hpos := (le_iff_eventually (f := 0) rfl hf).mp hx
  apply Subtype.ext
  change Germ.map (fun r => |r| ^ (n⁻¹ : ℝ)) (x : Germs) ^ n = x
  rw [← hf, Germ.map_coe, ← Germ.coe_pow]
  exact Germ.coe_eq.mpr (hpos.mono fun s (hs : 0 ≤ f s) => by
    show (|f s| ^ (n⁻¹ : ℝ)) ^ n = f s
    rw [abs_of_nonneg hs, Real.rpow_inv_natCast_pow hs hn])

/-- Every nonnegative element has a nonnegative `n`-th root. -/
theorem exists_pow_eq_of_nonneg {n : ℕ} (hn : n ≠ 0) {x : Number} (hx : 0 ≤ x) :
    ∃ y, 0 ≤ y ∧ y ^ n = x :=
  ⟨nthRoot n hn x, nthRoot_nonneg n hn x, nthRoot_pow n hn hx⟩

/-- Every element has every odd root. -/
theorem exists_pow_eq_of_odd {n : ℕ} (hn : Odd n) (x : Number) : ∃ y, y ^ n = x := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  rcases le_total 0 x with hx | hx
  · exact ⟨nthRoot n hn0 x, nthRoot_pow n hn0 hx⟩
  · refine ⟨-nthRoot n hn0 (-x), ?_⟩
    rw [hn.neg_pow, nthRoot_pow n hn0 (neg_nonneg.mpr hx), neg_neg]

theorem sqrt_mul_self {x : Number} (hx : 0 ≤ x) : sqrt x * sqrt x = x := by
  obtain ⟨⟨f, hf, -⟩, -⟩ := mem x
  have hpos := (le_iff_eventually (f := 0) rfl hf).mp hx
  apply Subtype.ext
  change Germ.map Real.sqrt (x : Germs) * Germ.map Real.sqrt (x : Germs) = x
  rw [← hf, Germ.map_coe, ← Germ.coe_mul]
  exact Germ.coe_eq.mpr (hpos.mono fun s hs => Real.mul_self_sqrt hs)

end HyperAlgebraic
