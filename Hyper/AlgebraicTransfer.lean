import Hyper.OrderedRational
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.FieldTheory.RatFunc.Degree

/-! Transfer principle for the algebraic hyperreals ℝ(ω), ε = ω⁻¹.

Keisler's Axiom E ("every real solution of S is a solution of T") is a
universal sentence `∀ x⃗, S x⃗ → T x⃗`. For quantifier-free formulas built
from `+ · - ⁻¹`, real constants, `=` and `<` this transfers from ℝ to ℝ(ω)
without ultrafilters or Tarski: read ω as a large real `s`. Every hyperreal
has an eventually constant sign as `s → ∞`, which is exactly the order of
ℝ(ω), so every formula is eventually true or eventually false.

What does *not* transfer is `∀∃` (Keisler gets those from Axiom D, the
extension of every real function): see `no_sqrt_omega`. -/

noncomputable section
namespace AlgebraicTransfer
open Polynomial Filter AlgebraicHyperreal
open scoped AlgebraicHyperreal

abbrev Hyperreal := RatFunc ℝ

/-- The hyperreal `x` read at a concrete real `s` in place of ω. -/
def valueAt (x : Hyperreal) (s : ℝ) : ℝ := x.num.eval s / x.denom.eval s

/-! ### Polynomials have an eventual sign -/

theorem eventually_pos_of_leadingCoeff_pos {p : ℝ[X]} (h : 0 < p.leadingCoeff) :
    ∀ᶠ s in atTop, 0 < p.eval s := by
  by_cases hdeg : 0 < p.degree
  · exact (tendsto_atTop_of_leadingCoeff_nonneg p hdeg h.le).eventually_gt_atTop 0
  · have hn : p.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.mpr (not_lt.mp hdeg)
    refine Eventually.of_forall fun s => ?_
    rw [eq_C_of_natDegree_eq_zero hn, eval_C]
    simpa [leadingCoeff, hn] using h

theorem eventually_ne_zero {p : ℝ[X]} (hp : p ≠ 0) : ∀ᶠ s in atTop, p.eval s ≠ 0 := by
  rcases lt_or_gt_of_ne (leadingCoeff_ne_zero.mpr hp) with h | h
  · filter_upwards [eventually_pos_of_leadingCoeff_pos (p := -p) (by simpa using h)]
      with s hs
    simp only [eval_neg, neg_pos] at hs
    exact hs.ne
  · filter_upwards [eventually_pos_of_leadingCoeff_pos h] with s hs using hs.ne'

theorem eventually_denom_ne_zero (x : Hyperreal) : ∀ᶠ s in atTop, x.denom.eval s ≠ 0 :=
  eventually_ne_zero (RatFunc.denom_ne_zero x)

/-! ### Reading at `s` is eventually a field homomorphism -/

/-- Any fraction representing `x` gives its value, for large enough `s`. -/
theorem eventually_valueAt_eq_div {x : Hyperreal} {p q : ℝ[X]} (hq : q ≠ 0)
    (hx : x = algebraMap ℝ[X] Hyperreal p / algebraMap ℝ[X] Hyperreal q) :
    ∀ᶠ s in atTop, valueAt x s = p.eval s / q.eval s := by
  have injective := RatFunc.algebraMap_injective ℝ
  have hcross : x.num * q = p * x.denom := by
    apply injective
    rw [← RatFunc.num_div_denom x, div_eq_div_iff
      ((map_ne_zero_iff _ injective).mpr (RatFunc.denom_ne_zero x))
      ((map_ne_zero_iff _ injective).mpr hq)] at hx
    simpa only [map_mul] using hx
  filter_upwards [eventually_ne_zero hq, eventually_denom_ne_zero x] with s hqs hds
  rw [valueAt, div_eq_div_iff hds hqs]
  simpa only [eval_mul] using congrArg (eval s) hcross

/-- `x` as the quotient of its own numerator and denominator. -/
theorem num_div_denom' (x : Hyperreal) :
    x = algebraMap ℝ[X] Hyperreal x.num / algebraMap ℝ[X] Hyperreal x.denom :=
  (RatFunc.num_div_denom x).symm

theorem valueAt_const (r : ℝ) (s : ℝ) : valueAt (RatFunc.C r) s = r := by
  simp [valueAt]

theorem valueAt_zero (s : ℝ) : valueAt 0 s = 0 := by simp [valueAt]

theorem eventually_valueAt_add (x y : Hyperreal) :
    ∀ᶠ s in atTop, valueAt (x + y) s = valueAt x s + valueAt y s := by
  have hdx := RatFunc.denom_ne_zero x
  have hdy := RatFunc.denom_ne_zero y
  have hsum : x + y = algebraMap ℝ[X] Hyperreal (x.num * y.denom + x.denom * y.num) /
      algebraMap ℝ[X] Hyperreal (x.denom * y.denom) := by
    conv_lhs => rw [num_div_denom' x, num_div_denom' y]
    rw [div_add_div _ _ (RatFunc.algebraMap_ne_zero hdx) (RatFunc.algebraMap_ne_zero hdy)]
    simp only [map_add, map_mul]
  filter_upwards [eventually_valueAt_eq_div (mul_ne_zero hdx hdy) hsum,
    eventually_denom_ne_zero x, eventually_denom_ne_zero y] with s h hxs hys
  rw [h, valueAt, valueAt, div_add_div _ _ hxs hys]
  simp only [eval_add, eval_mul]

theorem eventually_valueAt_mul (x y : Hyperreal) :
    ∀ᶠ s in atTop, valueAt (x * y) s = valueAt x s * valueAt y s := by
  have hprod : x * y = algebraMap ℝ[X] Hyperreal (x.num * y.num) /
      algebraMap ℝ[X] Hyperreal (x.denom * y.denom) := by
    conv_lhs => rw [num_div_denom' x, num_div_denom' y]
    rw [div_mul_div_comm]
    simp only [map_mul]
  filter_upwards [eventually_valueAt_eq_div
    (mul_ne_zero (RatFunc.denom_ne_zero x) (RatFunc.denom_ne_zero y)) hprod] with s h
  rw [h, valueAt, valueAt, div_mul_div_comm]
  simp only [eval_mul]

theorem eventually_valueAt_neg (x : Hyperreal) :
    ∀ᶠ s in atTop, valueAt (-x) s = -valueAt x s := by
  have hneg : -x = algebraMap ℝ[X] Hyperreal (-x.num) / algebraMap ℝ[X] Hyperreal x.denom := by
    conv_lhs => rw [num_div_denom' x]
    rw [map_neg, neg_div]
  filter_upwards [eventually_valueAt_eq_div (RatFunc.denom_ne_zero x) hneg] with s h
  rw [h, valueAt, eval_neg, neg_div]

theorem eventually_valueAt_inv (x : Hyperreal) :
    ∀ᶠ s in atTop, valueAt x⁻¹ s = (valueAt x s)⁻¹ := by
  by_cases hx : x = 0
  · subst hx
    exact Eventually.of_forall fun s => by simp [valueAt_zero]
  have hinv : x⁻¹ = algebraMap ℝ[X] Hyperreal x.denom / algebraMap ℝ[X] Hyperreal x.num := by
    conv_lhs => rw [num_div_denom' x]
    rw [inv_div]
  filter_upwards [eventually_valueAt_eq_div (RatFunc.num_ne_zero hx) hinv] with s h
  rw [h, valueAt, inv_div]

theorem eventually_valueAt_sub (x y : Hyperreal) :
    ∀ᶠ s in atTop, valueAt (y - x) s = valueAt y s - valueAt x s := by
  filter_upwards [eventually_valueAt_add y (-x), eventually_valueAt_neg x] with s hadd hneg
  rw [sub_eq_add_neg, hadd, hneg, ← sub_eq_add_neg]

/-! ### The order of ℝ(ω) is the eventual order -/

theorem eventually_valueAt_pos {x : Hyperreal} (hx : 0 < x) :
    ∀ᶠ s in atTop, 0 < valueAt x s := by
  rw [pos_iff] at hx
  have hd : 0 < x.denom.leadingCoeff := by simp [(RatFunc.monic_denom x).leadingCoeff]
  filter_upwards [eventually_pos_of_leadingCoeff_pos hx, eventually_pos_of_leadingCoeff_pos hd]
    with s hn hds using div_pos hn hds

theorem eventually_valueAt_lt {x y : Hyperreal} (hxy : x < y) :
    ∀ᶠ s in atTop, valueAt x s < valueAt y s := by
  filter_upwards [eventually_valueAt_pos (sub_pos.mpr hxy), eventually_valueAt_sub x y]
    with s hpos hsub
  rw [hsub] at hpos
  exact sub_pos.mp hpos

/-! ### Syntax: quantifier-free formulas of ordered fields with real constants -/

inductive Term (n : ℕ) where
  | var : Fin n → Term n
  | const : ℝ → Term n
  | add : Term n → Term n → Term n
  | mul : Term n → Term n → Term n
  | neg : Term n → Term n
  | inv : Term n → Term n

/-- Evaluate in any field `F`, reading real constants through `embed`. -/
def Term.eval {n : ℕ} {F : Type*} [Field F] (embed : ℝ → F) (v : Fin n → F) : Term n → F
  | var i => v i
  | const r => embed r
  | add a b => a.eval embed v + b.eval embed v
  | mul a b => a.eval embed v * b.eval embed v
  | neg a => -a.eval embed v
  | inv a => (a.eval embed v)⁻¹

inductive Formula (n : ℕ) where
  | eq : Term n → Term n → Formula n
  | lt : Term n → Term n → Formula n
  | not : Formula n → Formula n
  | and : Formula n → Formula n → Formula n
  | or : Formula n → Formula n → Formula n

def Formula.imp {n : ℕ} (a b : Formula n) : Formula n := .or (.not a) b

def Formula.Holds {n : ℕ} {F : Type*} [Field F] [LT F] (embed : ℝ → F) (v : Fin n → F) :
    Formula n → Prop
  | eq a b => a.eval embed v = b.eval embed v
  | lt a b => a.eval embed v < b.eval embed v
  | not a => ¬a.Holds embed v
  | and a b => a.Holds embed v ∧ b.Holds embed v
  | or a b => a.Holds embed v ∨ b.Holds embed v

/-- The real tuple obtained by reading every hyperreal coordinate at `s`. -/
def realize {n : ℕ} (v : Fin n → Hyperreal) (s : ℝ) : Fin n → ℝ := fun i => valueAt (v i) s

theorem Term.eventually_valueAt {n : ℕ} (v : Fin n → Hyperreal) :
    ∀ t : Term n, ∀ᶠ s in atTop, valueAt (t.eval RatFunc.C v) s = t.eval id (realize v s)
  | var i => Eventually.of_forall fun _ => rfl
  | const r => Eventually.of_forall fun s => valueAt_const r s
  | add a b => by
    filter_upwards [eventually_valueAt_add (a.eval RatFunc.C v) (b.eval RatFunc.C v),
      a.eventually_valueAt v, b.eventually_valueAt v] with s h ha hb
    simp only [Term.eval, h, ha, hb]
  | mul a b => by
    filter_upwards [eventually_valueAt_mul (a.eval RatFunc.C v) (b.eval RatFunc.C v),
      a.eventually_valueAt v, b.eventually_valueAt v] with s h ha hb
    simp only [Term.eval, h, ha, hb]
  | neg a => by
    filter_upwards [eventually_valueAt_neg (a.eval RatFunc.C v), a.eventually_valueAt v]
      with s h ha
    simp only [Term.eval, h, ha]
  | inv a => by
    filter_upwards [eventually_valueAt_inv (a.eval RatFunc.C v), a.eventually_valueAt v]
      with s h ha
    simp only [Term.eval, h, ha]

/-- Each atom is decided eventually, the same way as in ℝ(ω). -/
theorem atom_decided {n : ℕ} (v : Fin n → Hyperreal) (a b : Term n)
    (atom : ℝ → ℝ → Prop) (hyperAtom : Hyperreal → Hyperreal → Prop)
    (decided : ∀ x y, (hyperAtom x y → ∀ᶠ s in atTop, atom (valueAt x s) (valueAt y s)) ∧
      (¬hyperAtom x y → ∀ᶠ s in atTop, ¬atom (valueAt x s) (valueAt y s))) :
    (hyperAtom (a.eval RatFunc.C v) (b.eval RatFunc.C v) →
        ∀ᶠ s in atTop, atom (a.eval id (realize v s)) (b.eval id (realize v s))) ∧
      (¬hyperAtom (a.eval RatFunc.C v) (b.eval RatFunc.C v) →
        ∀ᶠ s in atTop, ¬atom (a.eval id (realize v s)) (b.eval id (realize v s))) := by
  have values := (a.eventually_valueAt v).and (b.eventually_valueAt v)
  constructor <;> intro h
  · filter_upwards [(decided _ _).1 h, values] with s hs ⟨ha, hb⟩
    rwa [← ha, ← hb]
  · filter_upwards [(decided _ _).2 h, values] with s hs ⟨ha, hb⟩
    rwa [← ha, ← hb]

theorem eq_decided (x y : Hyperreal) :
    (x = y → ∀ᶠ s in atTop, valueAt x s = valueAt y s) ∧
      (x ≠ y → ∀ᶠ s in atTop, valueAt x s ≠ valueAt y s) := by
  refine ⟨fun h => Eventually.of_forall fun s => by rw [h], fun h => ?_⟩
  rcases lt_or_gt_of_ne h with hlt | hgt
  · filter_upwards [eventually_valueAt_lt hlt] with s hs using hs.ne
  · filter_upwards [eventually_valueAt_lt hgt] with s hs using hs.ne'

theorem lt_decided (x y : Hyperreal) :
    (x < y → ∀ᶠ s in atTop, valueAt x s < valueAt y s) ∧
      (¬x < y → ∀ᶠ s in atTop, ¬valueAt x s < valueAt y s) := by
  refine ⟨eventually_valueAt_lt, fun h => ?_⟩
  rcases (not_lt.mp h).lt_or_eq with hlt | heq
  · filter_upwards [eventually_valueAt_lt hlt] with s hs using not_lt.mpr hs.le
  · exact Eventually.of_forall fun s => by rw [heq]; exact lt_irrefl _

theorem Formula.eventually_decided {n : ℕ} (v : Fin n → Hyperreal) :
    ∀ φ : Formula n, (φ.Holds RatFunc.C v → ∀ᶠ s in atTop, φ.Holds id (realize v s)) ∧
      (¬φ.Holds RatFunc.C v → ∀ᶠ s in atTop, ¬φ.Holds id (realize v s))
  | eq a b => atom_decided v a b _ _ eq_decided
  | lt a b => atom_decided v a b _ _ lt_decided
  | not a => by
    obtain ⟨hpos, hneg⟩ := a.eventually_decided v
    exact ⟨hneg, fun h => (hpos (not_not.mp h)).mono fun _ hs => not_not.mpr hs⟩
  | and a b => by
    obtain ⟨hapos, haneg⟩ := a.eventually_decided v
    obtain ⟨hbpos, hbneg⟩ := b.eventually_decided v
    refine ⟨fun ⟨ha, hb⟩ => (hapos ha).and (hbpos hb), fun h => ?_⟩
    rcases not_and_or.mp h with ha | hb
    · exact (haneg ha).mono fun _ hs hab => hs hab.1
    · exact (hbneg hb).mono fun _ hs hab => hs hab.2
  | or a b => by
    obtain ⟨hapos, haneg⟩ := a.eventually_decided v
    obtain ⟨hbpos, hbneg⟩ := b.eventually_decided v
    refine ⟨fun h => h.elim (fun ha => (hapos ha).mono fun _ => Or.inl)
      (fun hb => (hbpos hb).mono fun _ => Or.inr), fun h => ?_⟩
    obtain ⟨ha, hb⟩ := not_or.mp h
    exact ((haneg ha).and (hbneg hb)).mono fun _ ⟨hsa, hsb⟩ hab => hab.elim hsa hsb

/-- **Transfer.** A quantifier-free statement true for all real tuples is true
for all hyperreal tuples (Keisler's Axiom E for field operations). -/
theorem transfer {n : ℕ} (φ : Formula n) (holdsReal : ∀ v : Fin n → ℝ, φ.Holds id v)
    (v : Fin n → Hyperreal) : φ.Holds RatFunc.C v := by
  by_contra fails
  obtain ⟨s, hs⟩ := ((φ.eventually_decided v).2 fails).exists
  exact hs (holdsReal _)

/-! ### The boundary: `∀∃` does not transfer -/

theorem real_sqrt_exists (x : ℝ) (hx : 0 < x) : ∃ y : ℝ, y * y = x :=
  ⟨Real.sqrt x, Real.mul_self_sqrt hx.le⟩

/-- ω is positive but has no square root in ℝ(ω): its degree 1 is odd. -/
theorem no_sqrt_omega : ¬∃ y : Hyperreal, y * y = AlgebraicHyperreal.omega := by
  rintro ⟨y, hy⟩
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact omega_ne_zero (by simpa using hy.symm)
  have hdeg := congrArg RatFunc.intDegree hy
  rw [RatFunc.intDegree_mul hy0 hy0, AlgebraicHyperreal.omega, RatFunc.intDegree_X] at hdeg
  omega

end AlgebraicTransfer
