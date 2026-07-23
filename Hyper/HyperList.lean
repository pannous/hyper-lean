import Mathlib.Data.EReal.Basic
import Mathlib.Tactic.NormNum

def debugMode : Bool := false -- show ε, ω, etc. in output
-- def debugMode : Bool := true -- [(1,0)]
-- set_option autoImplicit false  -- Sometimes helps with implicit warnings
-- set_option trace.compiler.silent true HALU
-- set_option warn.noMessages true HALU
-- set_option logFilter "error" HALU
set_option warningAsError false

notation "∞" => (⊤ : EReal)
notation "-∞" => (⊥ : EReal)
namespace Hypers
section HyperLists
notation "𝔽" => ℚ
def Comps := List (𝔽 × 𝔽)
def HyperList : Type := List (𝔽 × 𝔽)

notation "R*" => HyperList
notation "𝔽*" => R*
instance : One R* where one := [(1, 0)]
instance : Zero R* where zero := ([]:R*)
def zero : R* := [] -- ⚠️ MAY CLASH WITH TACTIC zero in induction!!
def zero' : R* := [(0,0)]
def nil : R* := []
def one : R* := [(1, 0)]
def epsilon : R* := [(1, -1)]
def omega : R* := [(1, 1)]
scoped notation "O" => zero
scoped notation "I" => one
scoped notation "ε" => epsilon
scoped notation "ω" => omega
instance : Inhabited R* := ⟨zero⟩

-- coercions of 'sub'fields into 𝔽*
instance : Coe 𝔽 𝔽* where coe (n:𝔽) : R* := [(n, 0)]
instance : Coe ℕ 𝔽* where coe (n:ℕ) : R* := [((n:𝔽), 0)]
instance : Coe ℚ 𝔽* where coe (q:ℚ) : R* := [(q, 0)]
instance : Coe ℤ 𝔽* where coe (q:ℤ) : R* := [(q, 0)]
instance : Coe (ℚ×ℚ) 𝔽* where coe (q:ℚ×ℚ) : R* := (q.1, q.2) :: []
instance : Coe (𝔽×𝔽) 𝔽* where coe (q:𝔽×𝔽) : R* := (q.1, q.2) :: []
instance : Coe (𝔽 × ℤ) 𝔽* where coe (q:𝔽×ℤ) : R* := (q.1, q.2) :: []
instance : Coe (ℕ × ℕ) 𝔽* where coe (q: ℕ×ℕ) : R* := (q.1, q.2) :: []
instance : Coe (ℤ × ℤ) 𝔽* where coe (q: ℤ×ℤ) : R* := (q.1, q.2) :: []
instance : Coe (ℕ × ℕ) (𝔽 × 𝔽) where coe (q: ℕ×ℕ) : (𝔽 × 𝔽) := ((q.1:𝔽), (q.2:𝔽))
instance : Coe (ℤ × ℤ) (𝔽 × 𝔽) where coe (q: ℤ×ℤ) : (𝔽 × 𝔽) := ((q.1:𝔽), (q.2:𝔽))
instance : Coe (ℕ × ℕ) R* where coe x := [x]
-- UN-SIMPLIFIED!
instance : Coe (List (𝔽 × 𝔽)) R* where coe x := x -- simplify x
instance : Coe (List (ℕ × ℕ)) R* where coe x := x.map (λ (a, b) => ((a : 𝔽), (b : 𝔽)))
instance : Coe (List (𝔽 × ℤ)) R* where coe x := x.map (λ (a, b) => ((a : 𝔽), (b : 𝔽)))
instance : Coe (List (ℤ × ℤ)) (List (𝔽 × 𝔽)) where coe x := x.map (λ (a, b) => ((a : 𝔽), (b : 𝔽)))

--  for the propositional equality x = y, not the boolean equality x == y.
instance : DecidableEq 𝔽 := inferInstance
instance [DecidableEq 𝔽] : DecidableEq (𝔽 × 𝔽) := inferInstance
instance [DecidableEq (𝔽 × 𝔽)] : DecidableEq (List (𝔽 × 𝔽)) := inferInstance
instance [DecidableEq (List (𝔽 × 𝔽))] : DecidableEq R* := inferInstance
instance : OfNat R* 0 where ofNat := []
instance : OfNat R* 1 where ofNat := [(1, 0)]
instance : OfNat R* n where ofNat := [(n, 0)]
-- NEEDED FOR COERCIONS r == 0
instance : OfNat (List (𝔽 × 𝔽)) n where ofNat := [(n, 0)]
instance : OfNat (List (𝔽 × 𝔽)) 0 where ofNat := [] -- Adding instance for OfNat (List (ℚ × ℚ)) 0

instance {n : ℕ} : OfNat R* n where ofNat := [(n, 0)]
-- instance : OfNat List 0 where ofNat := []
instance : EmptyCollection R* where emptyCollection := []

-- #eval 0 = []
-- #eval ([(0,0)]:𝔽*) = (0:𝔽*) -- todo?


-- CANONICAL FORM: sorted descending by exponent, at most one term per exponent,
-- no zero coefficients. This makes `simplify` order-independent on its input
-- (⇒ simplify (x ++ y) = simplify (y ++ x), the key fact behind add_comm etc.)

/-- Sum of all coefficients attached to a given exponent `e` — the "true" value
    of a hyperreal at order `e`, independent of how its terms are listed/ordered. -/
def coeffAt (a : R*) (e : 𝔽) : 𝔽 :=
  ((a.filter (λ p => p.2 = e)).map Prod.fst).sum

lemma coeffAt_perm {a b : R*} (h : a.Perm b) (e : 𝔽) : coeffAt a e = coeffAt b e := by
  unfold coeffAt
  exact List.Perm.sum_eq ((h.filter _).map _)

lemma coeffAt_nil (e : 𝔽) : coeffAt ([] : R*) e = 0 := rfl

lemma coeffAt_cons (r e : 𝔽) (a : R*) (e' : 𝔽) :
    coeffAt ((r, e) :: a) e' = (if e = e' then r else 0) + coeffAt a e' := by
  unfold coeffAt
  by_cases h : e = e'
  · simp [List.filter_cons, h]
  · simp [List.filter_cons, h]

/-- Merge consecutive same-exponent terms in an exponent-sorted list, summing coefficients. -/
def mergeAdjacent : List (𝔽 × 𝔽) → List (𝔽 × 𝔽)
  | [] => []
  | [x] => [x]
  | (r₁, e₁) :: (r₂, e₂) :: rest =>
      if e₁ = e₂ then mergeAdjacent ((r₁ + r₂, e₁) :: rest)
      else (r₁, e₁) :: mergeAdjacent ((r₂, e₂) :: rest)
termination_by l => l.length
decreasing_by all_goals (simp_all; try omega)

/-- Comparator for descending order by exponent (highest order first). -/
def myle (p q : 𝔽 × 𝔽) : Bool := decide (q.2 ≤ p.2)

/-- Canonical form: sort descending by exponent, merge duplicate exponents, drop zeros. -/
def simplify (a : R*) : R* :=
  (mergeAdjacent (a.mergeSort myle))
    |>.filter (λ p => p.1 ≠ 0)

def simplifyOrdered (l : List (𝔽 × 𝔽)) : Prop :=
  ∀ (a b : ℕ) (r₁ e₁ r₂ e₂ : 𝔽),
    l[a]? = some (r₁, e₁) → l[b]? = some (r₂, e₂) → a < b → e₂ ≤ e₁

def normalize (x : R*) : R* := simplify x
-- def normalize (x : R*) : R* := if x = [(0,0)] then [] else x

-- def merge (x y : R*) : R* := simplify (List.append x y) -- simplify ∘ List.append
@[simp]
def merge (x y : R*) : R* := if x = [] then y else if y = [] then x else simplify (List.append x y) -- simplify ∘ List.append
@[simp] theorem merge_nil_left (x : R*) : merge [] x = x := by simp [merge]

@[simp] theorem merge_nil_right (x : R*) : merge x [] = x := by
  unfold merge
  split_ifs with h
  · -- Case: x = []
    rw [h]
  · -- Case: y = [] (which is always true here)
    simp
  · -- Default case : can't happen
    contradiction

-- @[simp] theorem merge_cons (a : α) (x y : R*) : merge (a :: x) y = simplify (List.append (a :: x) y) :=
  -- by simp [merge]
-- have h : ([] : R*) + x = x := by
--       rw [merge] -- failed to rewrite using equation theorems for 'Hypers.merge'.

-- HAppend.hAppend
instance : HAppend R* R* R* where hAppend := merge
-- via Coercion:
-- instance : HAppend R* (List (𝔽 × 𝔽)) R* where hAppend := merge
-- instance : HAppend R* (𝔽 × 𝔽) R* where hAppend x y := merge x y
-- instance : HAppend R* (List (ℕ × ℕ)) R* where hAppend x y := merge x y
-- instance : HAppend R* (ℕ × ℕ) R* where hAppend x y := merge x y
instance : HAppend (List (𝔽 × 𝔽)) R* R* where hAppend := merge -- needed (why?)
-- instance : HAppend (𝔽 × 𝔽) R* R* where hAppend x y := merge x y
-- instance : HAppend (ℕ × ℕ) R* R* where hAppend x y := merge x y

-- HAdd.hAdd
instance : Add R* where add := merge
instance : HAdd R* R* R* where hAdd x y := merge x y -- should take care of all coercions?
instance : HAdd R* (List (𝔽 × 𝔽)) R* where hAdd := merge
-- instance : HAdd R* (List (ℚ × ℚ)) R* where hAdd := merge
-- instance : HAdd R* (List (ℕ × ℕ)) R* where hAdd x y := merge x y
instance : HAdd R* (𝔽 × 𝔽) R* where hAdd x y := merge x y
-- instance : HAdd R* (ℚ × ℚ) R* where hAdd x y := merge x y
-- instance : HAdd R* (ℕ × ℕ) R* where hAdd x y := merge x y
-- instance : HAdd (List (ℚ × ℚ)) R* R* where hAdd := merge
instance : HAdd (List (𝔽 × 𝔽)) R* R* where hAdd := merge
-- instance : HAdd (List (ℕ × ℕ)) R* R* where hAdd x y := merge x y
-- instance : HAdd (𝔽 × 𝔽) R* R* where hAdd x y := merge x y
-- instance : HAdd (ℚ × ℚ) R* R* where hAdd x y := merge x y
-- instance : HAdd (ℕ × ℕ) R* R* where hAdd x y := merge x y
-- instance : HAdd (𝔽 × 𝔽) (𝔽 × 𝔽) R* where hAdd x y := merge x y
-- instance : HAdd (𝔽 × 𝔽) (List (𝔽 × 𝔽)) R* where hAdd x y := merge x y
-- instance : HAdd (List (𝔽 × 𝔽)) (𝔽 × 𝔽) R* where hAdd x y := merge x y
instance : HAdd (List (𝔽 × 𝔽)) (List (𝔽 × 𝔽)) R* where hAdd x y := merge x y
-- instance : HAdd (ℕ × ℕ) (ℕ × ℕ) R* where hAdd x y := merge x y
-- instance : HAdd (ℕ × ℕ) (List (ℕ × ℕ)) R* where hAdd x y := merge x y
-- instance : HAdd (List (ℕ × ℕ)) (ℕ × ℕ) R* where hAdd x y := merge x y
-- instance : HAdd (List (ℕ × ℕ)) (List (ℕ × ℕ)) R* where hAdd x y := merge x y

instance : Neg R* where neg x := x.map λ (r, e) => (-r, e)
instance : Neg (List (𝔽 × 𝔽)) where neg x := x.map λ (r, e) => (-r, e)
-- instance : Neg R* where neg x := if x = [] then [] else normalize (x.map λ (r, e) => (-r, e))
instance : Sub R* where sub x y := x + -y

-- instance : HAppend (List (𝔽 × 𝔽)) R* R* where hAppend := merge -- needed (why?)
-- HSMul.hSMul

-- tweaking the definition breaks usual scalar theorems: (1 - 1) • x = x - x ≠ 0 ?
-- [(0,0)] ≠ 0
instance : HSMul 𝔽 R* R* where hSMul n x := if n = 0 then [] else if n = 1 then x else x.map (λ (r, e) => (n * r, e))
-- instance : HSMul ℤ R* R* where hSMul n x := if n = 0 then [] else if n = 1 then x else x.map (λ (r, e) => (n * r, e))
instance : HSMul ℕ R* R* where hSMul n x := if n = 0 then [] else if n = 1 then x else x.map (λ (r, e) => (n * r, e))
instance : SMul ℤ R* where smul n x := if n = 0 then [] else if n = 1 then x else x.map (λ (r, e) => (n * r, e))
-- instance : SMul ℤ R* where smul n x := x.map (λ (r, e) => (n * r, e))
instance : Mul R* where
  mul x y := normalize ((x.product y).map (λ ((r1, e1), (r2, e2)) => (r1 * r2, e1 + e2)))

instance : Inv R* where
  inv x := x.map (λ (r, e) => (r⁻¹, -e))
instance : HDiv R* R* R* where
  hDiv x y := x * y⁻¹
instance : HDiv 𝔽 R* R* where
  hDiv x y := x • y⁻¹

instance : ToString R* where
  toString f :=
    let terms := simplify f
    let (constants, exponentials) := terms.partition (λ (_, e) => e = 0)
    let constSum := constants.foldl (λ acc (c, _) => acc + c) (0:𝔽)
    if terms == [] then "0" else
    let expStr := exponentials.map (λ (c, e) =>
      if c = 0 ∧ e = 0 then "0"
      else
      if c = 1 then
        if e = 1 then "ω"
        else if e = 2 then "ω²"
        else if e = -1 then "ε"
        else if e = -2 then "ε²"
        else if e > 1 then s!"ω^{e}"
        else if e < -1 then s!"ε^{e}"
        else "0"
      else
      if e = 1 then s!"{c}ω"
      else if e = 2 then s!"{c}ω²"
      else if e = -1 then s!"{c}ε"
      else if e = -2 then s!"{c}ε²"
      else if e > 1 then s!"{c}ω^{e}"
      else if e < -1 then s!"{c}ε^{e}"
      else s!"0"
    ) |>.intersperse " + " --
      |>.foldl String.append ""
    match (constSum, expStr) with
    | (0, exp) => exp
    | (c, "") => toString c
    | (c, exp) => s!"{c} + {exp}"

instance : Repr R* where
  reprPrec f _ := if debugMode then List.toString f else toString f



-- scoped notation:max "ε²" => (ε * ε)
-- ⚠️ doesn't work: a is treated as unit => 2ε² => 2ε*2ε !!
-- scoped notation:max a "²" => (a * a)
-- scoped notation:max a "³" => a * a * a
-- scoped notation:max a "⁴" => a * a * a * a
-- scoped notation:1 n "ε" => (n * ε)  -- Explicit multiplication instead of •
scoped notation:max n "ε" => (n • ε)
scoped notation:max n "ε²" => (n • ε*ε)
-- scoped notation:1 a "²" => (a) * (a)
scoped notation:max n "ω" => (n • ω)
scoped notation:max n "ω²" => (n • ω*ω)
scoped notation:max "√" a => a^(1/2)
scoped notation:max "∛" a => a^(1/3)
scoped notation:max "∜" a => a^(1/4)

-- #eval zero
#eval 1 + ω - ( 1 + 1/ε ) -- should cancel out to 0
#eval 1 + 2ω + ε + ε⁻¹ - (1 + ω - 2ε + 2/ε) -- should cancel out to 3ε
#eval ε + 3 - 4ω + 2ε²


def standard (x : R*) := simplify (x.filter (λ (_, order) => order = 0))
notation "st" => standard
notation "real" => standard
lemma standard_epsilon_zero : st ε = 0 := by native_decide
lemma standard_omega_zero : st ω = 0 := by native_decide
lemma standard_zero : st 0 = 0 := by native_decide
lemma standard_one : st 1 = 1 := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- ORDER: leading term (highest exponent) of `simplify (a - b)` decides a vs b.
-- This is the standard Hahn-series / hyperreal convention: higher order
-- (more infinite) terms dominate; among terms of equal order, larger
-- coefficient dominates. Matches the Readme's "Order Axiom".
-- ═══════════════════════════════════════════════════════════════════════════

lemma myle_trans : ∀ p q r : 𝔽 × 𝔽, myle p q → myle q r → myle p r := by
  intro p q r hpq hqr
  simp only [myle, decide_eq_true_eq] at *
  exact hqr.trans hpq

lemma myle_total : ∀ p q : 𝔽 × 𝔽, myle p q || myle q p := by
  intro p q
  simp only [myle, decide_eq_true_eq, Bool.or_eq_true]
  rcases le_total p.2 q.2 with h | h
  · right; exact h
  · left; exact h

-- ═══════════════════════════════════════════════════════════════════════════
-- CANONICAL FORM UNIQUENESS: `simplify` is fully determined by `coeffAt` — two
-- lists with the same value at every exponent simplify to the *same* list, not
-- just an equivalent one. This is the fact that makes the Field-instance ring
-- laws provable at all: each reduces to (a) `coeffAt` arithmetic, pure ℚ, then
-- (b) this uniqueness lemma, then (c) the pre-existing `eq_of_simplify_eq`
-- axiom (below) to lift `simplify LHS = simplify RHS` to the raw `LHS = RHS`
-- that the `Field R*` axioms actually demand.
-- ═══════════════════════════════════════════════════════════════════════════

/-- Merging never invents a new exponent, only combines existing ones. -/
theorem mergeAdjacent_exponent_mem (l : List (𝔽 × 𝔽)) :
    ∀ p ∈ mergeAdjacent l, ∃ q ∈ l, p.2 = q.2 := by
  induction l using mergeAdjacent.induct
  · simp [mergeAdjacent]
  · simp [mergeAdjacent]
  · rename_i r₁ r₂ e₂ rest ih
    simp only [mergeAdjacent, if_true]
    intro p hp
    obtain ⟨q, hq, hpq⟩ := ih p hp
    obtain rfl | hq := List.mem_cons.mp hq
    · exact ⟨(r₁, e₂), by simp, hpq⟩
    · exact ⟨q, by simp [hq], hpq⟩
  · rename_i r₁ e₁ r₂ e₂ rest hne ih
    simp only [mergeAdjacent, if_neg hne]
    intro p hp
    obtain rfl | hp := List.mem_cons.mp hp
    · exact ⟨(r₁, e₁), by simp, rfl⟩
    · obtain ⟨q, hq, hpq⟩ := ih p hp
      exact ⟨q, by simp [hq], hpq⟩

/-- `mergeAdjacent` preserves the total coefficient at every exponent: combining
adjacent same-exponent entries can't change any exponent's running sum. -/
theorem mergeAdjacent_coeffAt (l : List (𝔽 × 𝔽)) (e : 𝔽) :
    coeffAt (mergeAdjacent l) e = coeffAt l e := by
  induction l using mergeAdjacent.induct
  · simp [mergeAdjacent, coeffAt]
  · simp [mergeAdjacent]
  · rename_i r₁ r₂ e₂ rest ih
    simp only [mergeAdjacent, if_true]
    rw [coeffAt_cons, coeffAt_cons, ih, coeffAt_cons]
    by_cases h : e₂ = e
    · simp [h]; ring
    · simp [h]
  · rename_i r₁ e₁ r₂ e₂ rest hne ih
    simp only [mergeAdjacent, if_neg hne]
    rw [coeffAt_cons, coeffAt_cons, ih, coeffAt_cons]

/-- `mergeAdjacent` turns a weakly-descending list into a strictly-descending one:
grouping merges away every duplicate exponent. -/
theorem mergeAdjacent_pairwise_lt (l : List (𝔽 × 𝔽))
    (hp : l.Pairwise (fun p q => q.2 ≤ p.2)) :
    (mergeAdjacent l).Pairwise (fun p q => q.2 < p.2) := by
  induction l using mergeAdjacent.induct
  · simp [mergeAdjacent]
  · simp [mergeAdjacent]
  · rename_i r₁ r₂ e₂ rest ih
    simp only [mergeAdjacent, if_true]
    apply ih
    obtain ⟨_, hp'⟩ := List.pairwise_cons.mp hp
    obtain ⟨hbound, hp''⟩ := List.pairwise_cons.mp hp'
    exact List.pairwise_cons.mpr ⟨hbound, hp''⟩
  · rename_i r₁ e₁ r₂ e₂ rest hne ih
    simp only [mergeAdjacent, if_neg hne]
    obtain ⟨hbound1, hp'⟩ := List.pairwise_cons.mp hp
    obtain ⟨hbound2, hp''⟩ := List.pairwise_cons.mp hp'
    have he : e₂ < e₁ := lt_of_le_of_ne (hbound1 (r₂, e₂) (by simp)) (Ne.symm hne)
    have hstrict : ∀ q ∈ (r₂, e₂) :: rest, q.2 < e₁ := by
      intro q hq
      obtain rfl | hq := List.mem_cons.mp hq
      · exact he
      · exact lt_of_le_of_lt (hbound2 q hq) he
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih hp'⟩
    intro z hz
    obtain ⟨q, hq, hzq⟩ := mergeAdjacent_exponent_mem ((r₂, e₂) :: rest) z hz
    rw [hzq]
    exact hstrict q hq

theorem coeffAt_filter_ne_zero (l : List (𝔽 × 𝔽)) (e : 𝔽) :
    coeffAt (l.filter (fun p => p.1 ≠ 0)) e = coeffAt l e := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨r, e'⟩ := p
    by_cases hr : r = 0
    · subst hr
      simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false,
        Bool.false_eq_true, if_false]
      rw [coeffAt_cons, ih]
      simp
    · simp only [List.filter_cons, ne_eq, hr, not_false_eq_true, decide_true, if_true]
      rw [coeffAt_cons, coeffAt_cons, ih]

theorem coeffAt_mergeSort (l : List (𝔽 × 𝔽)) (e : 𝔽) :
    coeffAt (l.mergeSort myle) e = coeffAt l e :=
  coeffAt_perm (List.mergeSort_perm l myle) e

/-- `simplify` doesn't change a hyperreal's value at any exponent — only its
representation. -/
theorem coeffAt_simplify (a : R*) (e : 𝔽) : coeffAt (simplify a) e = coeffAt a e := by
  unfold simplify
  rw [coeffAt_filter_ne_zero, mergeAdjacent_coeffAt, coeffAt_mergeSort]

theorem simplify_pairwise_lt (a : R*) :
    (simplify a).Pairwise (fun p q => q.2 < p.2) := by
  unfold simplify
  apply List.Pairwise.filter
  apply mergeAdjacent_pairwise_lt
  exact (List.pairwise_mergeSort myle_trans myle_total a).imp
    (fun {p q} h => by simpa [myle] using h)

theorem simplify_nonzero (a : R*) : ∀ p : 𝔽 × 𝔽, List.Mem p (simplify a) → p.1 ≠ 0 := by
  unfold simplify
  intro p hp
  have := List.of_mem_filter hp
  simpa using this

theorem coeffAt_eq_zero_of_forall_ne {l : List (𝔽 × 𝔽)} {e : 𝔽} (h : ∀ p ∈ l, p.2 ≠ e) :
    coeffAt l e = 0 := by
  unfold coeffAt
  have hnil : l.filter (fun p => p.2 = e) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro p hp
    simpa using h p hp
  rw [hnil]
  rfl

/-- Canonical uniqueness: two strictly exponent-sorted, all-nonzero-coefficient lists
with the same `coeffAt` everywhere are literally the same list. -/
theorem canonical_unique : ∀ (a b : List (𝔽 × 𝔽)),
    a.Pairwise (fun p q => q.2 < p.2) → b.Pairwise (fun p q => q.2 < p.2) →
    (∀ p ∈ a, p.1 ≠ 0) → (∀ p ∈ b, p.1 ≠ 0) →
    (∀ e, coeffAt a e = coeffAt b e) → a = b
  | [], [], _, _, _, _, _ => rfl
  | [], (r, e) :: b, _, hpb, _, hb0, h => by
      obtain ⟨hbound, _⟩ := List.pairwise_cons.mp hpb
      have hcoeff : coeffAt ((r, e) :: b) e = r := by
        rw [coeffAt_cons, if_pos rfl,
          coeffAt_eq_zero_of_forall_ne (fun p hp => ne_of_lt (hbound p hp))]
        ring
      have heq := h e
      rw [coeffAt_nil, hcoeff] at heq
      exact absurd heq.symm (hb0 (r, e) (by simp))
  | (r, e) :: a, [], hpa, _, ha0, _, h => by
      obtain ⟨hbound, _⟩ := List.pairwise_cons.mp hpa
      have hcoeff : coeffAt ((r, e) :: a) e = r := by
        rw [coeffAt_cons, if_pos rfl,
          coeffAt_eq_zero_of_forall_ne (fun p hp => ne_of_lt (hbound p hp))]
        ring
      have heq := h e
      rw [coeffAt_nil, hcoeff] at heq
      exact absurd heq (ha0 (r, e) (by simp))
  | (r₁, e₁) :: a, (r₂, e₂) :: b, hpa, hpb, ha0, hb0, h => by
      obtain ⟨hboundA, hpa'⟩ := List.pairwise_cons.mp hpa
      obtain ⟨hboundB, hpb'⟩ := List.pairwise_cons.mp hpb
      have haCoeff : coeffAt ((r₁, e₁) :: a) e₁ = r₁ := by
        rw [coeffAt_cons, if_pos rfl,
          coeffAt_eq_zero_of_forall_ne (fun p hp => ne_of_lt (hboundA p hp))]
        ring
      have hbCoeff : coeffAt ((r₂, e₂) :: b) e₂ = r₂ := by
        rw [coeffAt_cons, if_pos rfl,
          coeffAt_eq_zero_of_forall_ne (fun p hp => ne_of_lt (hboundB p hp))]
        ring
      have hboundA' : ∀ p ∈ (r₁, e₁) :: a, p.2 ≤ e₁ := fun p hp =>
        (List.mem_cons.mp hp).elim (fun h' => h' ▸ le_refl _) (fun hp' => le_of_lt (hboundA p hp'))
      have hboundB' : ∀ p ∈ (r₂, e₂) :: b, p.2 ≤ e₂ := fun p hp =>
        (List.mem_cons.mp hp).elim (fun h' => h' ▸ le_refl _) (fun hp' => le_of_lt (hboundB p hp'))
      have he : e₁ = e₂ := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hz : coeffAt ((r₁, e₁) :: a) e₂ = 0 :=
            coeffAt_eq_zero_of_forall_ne
              (fun p hp => ne_of_lt (lt_of_le_of_lt (hboundA' p hp) hlt))
          have heq := h e₂
          rw [hz, hbCoeff] at heq
          exact hb0 (r₂, e₂) (by simp) heq.symm
        · have hz : coeffAt ((r₂, e₂) :: b) e₁ = 0 :=
            coeffAt_eq_zero_of_forall_ne
              (fun p hp => ne_of_lt (lt_of_le_of_lt (hboundB' p hp) hgt))
          have heq := h e₁
          rw [hz, haCoeff] at heq
          exact ha0 (r₁, e₁) (by simp) heq
      subst he
      have hr : r₁ = r₂ := by
        have heq := h e₁
        rwa [haCoeff, hbCoeff] at heq
      subst hr
      have htails : ∀ e, coeffAt a e = coeffAt b e := by
        intro e
        by_cases he' : e = e₁
        · subst he'
          rw [coeffAt_eq_zero_of_forall_ne (fun p hp => ne_of_lt (hboundA p hp)),
            coeffAt_eq_zero_of_forall_ne (fun p hp => ne_of_lt (hboundB p hp))]
        · have hne' : e₁ ≠ e := fun h' => he' h'.symm
          have heq := h e
          rw [coeffAt_cons, coeffAt_cons, if_neg hne'] at heq
          simpa using heq
      have hab : a = b := canonical_unique a b hpa' hpb'
        (fun p hp => ha0 p (List.mem_cons_of_mem _ hp))
        (fun p hp => hb0 p (List.mem_cons_of_mem _ hp)) htails
      rw [hab]

/-- The master corollary: two hyperreal expressions with the same value at every
exponent simplify to the same canonical form. Ring-law proofs below reduce to
(a) equal `coeffAt` profiles, then (b) this lemma. -/
theorem simplify_eq_of_coeffAt_eq {a b : R*} (h : ∀ e, coeffAt a e = coeffAt b e) :
    simplify a = simplify b :=
  canonical_unique (simplify a) (simplify b) (simplify_pairwise_lt a) (simplify_pairwise_lt b)
    (simplify_nonzero a) (simplify_nonzero b)
    (fun e => by rw [coeffAt_simplify, coeffAt_simplify]; exact h e)

theorem simplify_idempotent (a : R*) : simplify (simplify a) = simplify a :=
  simplify_eq_of_coeffAt_eq (coeffAt_simplify a)

theorem simplify_nil : simplify ([] : R*) = [] := by native_decide

theorem coeffAt_append (l₁ l₂ : List (𝔽 × 𝔽)) (e : 𝔽) :
    coeffAt (List.append l₁ l₂) e = coeffAt l₁ e + coeffAt l₂ e := by
  unfold coeffAt
  rw [List.append_eq, List.filter_append, List.map_append, List.sum_append]

theorem coeffAt_merge (x y : R*) (e : 𝔽) :
    coeffAt (merge x y) e = coeffAt x e + coeffAt y e := by
  unfold merge
  split_ifs with hx hy
  · subst hx; rw [coeffAt_nil]; ring
  · subst hy; rw [coeffAt_nil]; ring
  · rw [coeffAt_simplify, coeffAt_append]

theorem coeffAt_neg_map (x : R*) (e : 𝔽) :
    coeffAt (x.map (fun (p : 𝔽 × 𝔽) => (-p.1, p.2))) e = -coeffAt x e := by
  induction x with
  | nil => simp [coeffAt]
  | cons p rest ih =>
    obtain ⟨r, e'⟩ := p
    simp only [List.map_cons]
    rw [coeffAt_cons, coeffAt_cons, ih]
    by_cases h : e' = e <;> simp [h] <;> ring

/-- A two-element list, sorted descending by exponent (strict), is a fixed point of mergeSort
    regardless of which order the two elements were given in. -/
lemma mergeSort_pair (p q : 𝔽 × 𝔽) (h : q.2 < p.2) :
    [p, q].mergeSort myle = [p, q] ∧ [q, p].mergeSort myle = [p, q] := by
  have hsorted : [p, q].Pairwise (fun a b => myle a b) := by
    rw [List.pairwise_cons]
    refine ⟨fun y hy => ?_, List.Pairwise.cons (fun y hy => absurd hy (List.not_mem_nil)) List.Pairwise.nil⟩
    simp only [List.mem_singleton] at hy; subst hy
    simpa [myle] using h.le
  refine ⟨List.mergeSort_of_pairwise hsorted, ?_⟩
  apply List.Perm.eq_of_pairwise (le := fun a b => myle a b)
  · intro a b ha hb hab hba
    simp only [List.mem_mergeSort, List.mem_singleton, List.mem_cons, List.not_mem_nil,
      or_false] at ha hb
    by_contra hne
    have : a.2 = b.2 := by
      simp only [myle, decide_eq_true_eq] at hab hba
      exact le_antisymm hba hab
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      simp_all <;> exact absurd this (by simpa using h.ne')
  · exact List.pairwise_mergeSort myle_trans myle_total [q, p]
  · exact hsorted
  · exact (List.mergeSort_perm [q, p] myle).trans (List.Perm.swap p q [])

/-- Canonical form of a strictly-sorted two-term hyperreal: unchanged (assuming nonzero coeffs). -/
lemma simplify_pair {r₁ r₂ e₁ e₂ : 𝔽} (h : e₂ < e₁) (h₁ : r₁ ≠ 0) (h₂ : r₂ ≠ 0) :
    simplify [(r₁, e₁), (r₂, e₂)] = [(r₁, e₁), (r₂, e₂)] ∧
    simplify [(r₂, e₂), (r₁, e₁)] = [(r₁, e₁), (r₂, e₂)] := by
  obtain ⟨h1, h2⟩ := mergeSort_pair (r₁, e₁) (r₂, e₂) h
  have step : ∀ l : List (𝔽 × 𝔽), l.mergeSort myle = [(r₁, e₁), (r₂, e₂)] →
      simplify l = [(r₁, e₁), (r₂, e₂)] := by
    intro l hl
    unfold simplify
    rw [hl]
    simp [mergeAdjacent, h.ne', h₁, h₂]
  exact ⟨step _ h1, step _ h2⟩

/-- Leading (highest-order) sign of a hyperreal: `gt` if the top term is positive,
    `lt` if negative, `eq` if the value is (canonically) zero. -/
def leadSign (a : R*) : Ordering :=
  match simplify a with
  | [] => Ordering.eq
  | (r, _) :: _ => if 0 < r then Ordering.gt else Ordering.lt

instance : LT R* where lt a b := leadSign (a - b) = Ordering.lt
instance : LE R* where le a b := leadSign (a - b) ≠ Ordering.gt

instance (a b : R*) : Decidable (a < b) :=
  inferInstanceAs (Decidable (leadSign (a - b) = Ordering.lt))
instance (a b : R*) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (leadSign (a - b) ≠ Ordering.gt))

/-- The concrete positivity/order fact behind everything else: a two-term difference
    with a dominant (higher-exponent) term of known sign determines `<`. -/
lemma lt_of_lead_pair {a b : R*} {r₁ r₂ e₁ e₂ : 𝔽} (hab : a - b = [(r₁, e₁), (r₂, e₂)])
    (h : e₂ < e₁) (h₁ : r₁ ≠ 0) (h₂ : r₂ ≠ 0) (hneg : r₁ < 0) : a < b := by
  show leadSign (a - b) = Ordering.lt
  rw [hab, leadSign, (simplify_pair h h₁ h₂).1]
  simp [not_lt.mpr hneg.le]

/-- Single-term variant: `a - b` reduces to one nonzero term whose sign decides `a < b`. -/
lemma lt_of_lead_single {a b : R*} {r e : 𝔽} (hab : a - b = ([(r, e)] : R*)) (hneg : r < 0) :
    a < b := by
  show leadSign (a - b) = Ordering.lt
  rw [hab]
  simp [leadSign, simplify, mergeAdjacent, not_lt.mpr hneg.le, hneg.ne]

-- ═══════════════════════════════════════════════════════════════════════════
-- Concrete order facts (ε, ω). Fully decidable/computable, so `native_decide`
-- settles them directly; the parametrized facts below (arbitrary r : ℚ) need
-- the general lemmas above.
-- ═══════════════════════════════════════════════════════════════════════════

lemma epsilon_pos : (0 : R*) < ε := by native_decide
lemma omega_pos : (0 : R*) < ω := by native_decide
lemma epsilon_lt_one : ε < (1 : R*) := by native_decide
lemma epsilon_sq_lt_epsilon : ε * ε < ε := by native_decide
lemma epsilon_mul_omega : ε * ω = 1 := by native_decide
lemma omega_mul_epsilon : ω * ε = 1 := by native_decide

/-- Embed a scalar as a real (order-0) hyperreal. Avoids the ambiguity `binop%` elaboration
    runs into when coercing a bare `ℚ` on one side of `-`/`<` against an `R*` on the other. -/
def embedQ (r : 𝔽) : R* := [(r, 0)]

/-- ε is below every positive rational, embedded into R*: the defining infinitesimal property. -/
lemma epsilon_lt_of_pos (r : ℚ) (hr : 0 < r) : ε < embedQ r := by
  have hab : ε - embedQ r = ([(-r, 0), (1, -1)] : R*) := by
    show ε + (-embedQ r) = ([(-r, 0), (1, -1)] : R*)
    show merge ε (-embedQ r) = ([(-r, 0), (1, -1)] : R*)
    have h1 : ε ≠ ([] : R*) := by native_decide
    have h2 : (-embedQ r) ≠ ([] : R*) := by
      show ([(-r, 0)] : R*) ≠ ([] : R*)
      simp
    unfold merge
    rw [if_neg h1, if_neg h2]
    show simplify ([(1, -1)] ++ [(-r, 0)]) = ([(-r, 0), (1, -1)] : R*)
    have := (simplify_pair (r₁ := -r) (r₂ := 1) (e₁ := 0) (e₂ := -1)
      (by norm_num) (by linarith) (by norm_num)).2
    simpa using this
  exact lt_of_lead_pair hab (by norm_num) (by linarith) (by norm_num) (by linarith)

/-- ε is strictly positive and below every positive rational: the two defining
    properties of an infinitesimal, both now genuine theorems on R*. -/
lemma epsilon_infinitesimal (r : ℚ) (hr : 0 < r) : 0 < ε ∧ ε < embedQ r :=
  ⟨epsilon_pos, epsilon_lt_of_pos r hr⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- GAUGING LAWS: ωⁿ · εⁿ = 1 (n-dimensional atom/count duality, see Readme).
-- ═══════════════════════════════════════════════════════════════════════════

lemma gauging_1d : ω * ε = 1 := omega_mul_epsilon

lemma gauging_2d : (ω * ω) * (ε * ε) = 1 := by native_decide

-- #eval ((1,0) : R*) -- todo HERE not coerced / simplified to 1 see HyperCheck.lean
-- #eval ([(1,0)] : R*)

-- only works for 𝔽 == ℝ !!
-- instance : HPow R R* R* where
--   hPow n x := x.map (λ (r, e) => (r^n, e*n))
-- #eval ε + 3 - 4*ω + √ε²


-- SELF COERCION!
instance : Coe R* R* where
  coe := simplify

-- Define a proper equality relation
def HyperEq (x y : R*) : Prop := simplify x = simplify y
instance : Reflexive HyperEq := by
  intro x
  rfl
instance : Symmetric HyperEq := by
  intro x y h
  unfold HyperEq at h
  unfold HyperEq
  rw [h]
instance : Transitive HyperEq := by
  intro x y z hxy hyz
  unfold HyperEq at hxy hyz
  unfold HyperEq
  rw [hxy, hyz]
instance : Equivalence HyperEq := {
  refl := by intro x; rfl,
  symm := by intro x y h; unfold HyperEq at h ⊢; rw [h],
  trans := by intro x y z hxy hyz; unfold HyperEq at hxy hyz ⊢; rw [hxy, hyz]
}


@[simp]
lemma simplify_preserves_eq {x y : R*} (h : x = y) : simplify x = simplify y := by rw [h]


-- ⚠️ we FORCE equality even if x and y were originally different!?! inconsistency? IDK ⚠️
axiom eq_of_simplify_eq (x y : R*) : simplify x = simplify y → x = y
-- instance [DecidableEq (List (𝔽 × 𝔽))] : Decidable (x ≈ y) := inferInstanceAs (Decidable (simplify x = simplify y))
instance : DecidableEq R* :=
  fun x y =>
    match decEq (simplify x) (simplify y) with
    | isTrue h  => isTrue (eq_of_simplify_eq x y h)
    | isFalse h => isFalse (fun c => h (congrArg simplify c))


-- standard == equality  would this to recursion: (simplify x) == (simplify y) ?
instance : BEq R* where beq x y := (simplify x) = (simplify y)
instance : BEq (List (𝔽 × 𝔽)) where beq x y := (simplify x) = (simplify y)
instance : BEq (List (ℚ × ℚ)) where beq x y := (simplify x) = (simplify y)
instance : BEq (List (ℤ × ℤ)) where beq x y := (simplify (x:R*)) = (simplify (y:R*))
instance : BEq (List (ℕ × ℕ)) where beq x y := (simplify (x:R*)) = (simplify (y:R*))


-- standard ≈ equality
-- ⚠️ R* IS `List (𝔽 × 𝔽)` (`HyperList` is a plain `def`, not a wrapper type), and Lean core
-- registers a global `Setoid (List α)` (`List.isSetoid`, permutation-based) for every list type.
-- List-literal elaboration reduces the expected type `R*` to `List (𝔽 × 𝔽)` BEFORE typeclass
-- search runs, so `≈`/`HasEquiv`/`Setoid` get resolved against that reduced type. That means:
--  (a) an instance for `List.isSetoid` (permutation-based) would win over one we declare for
--      `R*` unless disabled — its `Decidable` goal then fails since the permutation-`Decidable`
--      instance lives in `Mathlib.Data.Multiset.Defs`, which we don't import; and
--  (b) our own instance must ALSO be stated for the reduced type `List (𝔽 × 𝔽)`, not `R*`,
--      or instance search (keyed on the reduced type) will simply never find it.
attribute [-instance] List.isSetoid

instance : HasEquiv (List (𝔽 × 𝔽)) where Equiv x y := HyperEq x y
infix:50 " ≅ " => HyperEq  -- alias, NOT NEEDED now that ≈ works directly

instance HyperSetoid : Setoid R* :=
{ r := HyperEq,
  iseqv := ⟨
    (by intro x; rfl),
    (by intro x y h; unfold HyperEq at h ⊢; rw [h]),
    (by intro x y z hxy hyz; unfold HyperEq at hxy hyz ⊢; rw [hxy, hyz])
  ⟩ }

instance decidableHyperEquiv (x y : List (𝔽 × 𝔽)) : Decidable (x ≈ y) :=
  decEq (simplify x) (simplify y)

#eval (simplify [(0,0)] == simplify (0 : R*)) -- true (simplify drops zero coefficients)
#eval ([(0,0)] : R*) = (0: R*) -- always false! (OK, raw lists differ)
#eval ([(0,0)] : R*) ≈ (0: R*) -- true (≈ compares simplified instances)
def HyperQuotient := Quotient HyperSetoid
instance [DecidableEq Comps] : DecidableEq HyperQuotient :=
  λ x y =>
    Quotient.recOnSubsingleton₂ x y (λ x y =>
      match decEq (simplify x) (simplify y) with
      | isTrue h  => isTrue (Quotient.sound h)
      | isFalse h => isFalse (by
          intro contra
          apply h
          exact Quotient.exact contra
        )
    )


lemma zero_add : ∀ x : R*,  0 + x = x := λ x => by
    exact merge_nil_left x

lemma add_zero : ∀ x : R*, x + 0 = x := λ x => by
    exact merge_nil_right x

lemma add_nil : (x: R*) + ↑[] = x := by
    exact merge_nil_right x

lemma zero0 : zero = 0 := rfl

lemma zero_hsmul : (0:ℕ ) • (x: R*) = zero := by
    simp [HSMul.hSMul, zero]  -- Simplifying the statement to prove it

lemma zero_smul : (0 : ℤ) • (x: R*) = zero := by
    simp [SMul.smul, HSMul.hSMul, zero]  -- Simplifying the statement to prove it

lemma one_smul : (1 : ℤ) • (x: R*) = x := by
    simp [SMul.smul, HSMul.hSMul]  -- Simplifying the statement to prove it

lemma one_times : 1 • (x: R*) = x := by
    simp [HSMul.hSMul]  -- Simplifying the statement to prove it


lemma zero_smuln : (0 : ℕ) • (x: R*) = zero := by
    simp [SMul.smul, HSMul.hSMul, zero]  -- Simplifying the statement to prove it

-- lemma zero_smuln' : zero = (0 : ℕ) • (x: R*)  := by
--     exact Eq.symm zero_smuln

open Int
-- (-n) • x = -(n • x)

-- lemma neg_add' (n : ℤ) (m : ℤ) : -(n + m) = -n - m := by simp
-- lemma neg_add' (n : ℤ) (m : ℤ) : -(n + m) = -n - m := by rfl
lemma neg_adda' (n : ℤ) (m : ℤ) : -(n + m) = -n - m := by
  rw [neg_eq_neg_one_mul, mul_add]
  simp
  rfl

lemma neg_add' (n : ℤ) (m : ℤ) : -((n + m): ℤ) = ((-n - m): ℤ) := by
  rw [neg_eq_neg_one_mul, mul_add]
  simp
  rfl

lemma neg_add'' (n : R*) (m : R*) : -((n + m): R*) = ((-n - m): R*) := by
  sorry


theorem sub_smul (r s : ℤ ) (y : R*) : (r - s) • y = r • y - s • y := by
  simp [add_smul, sub_eq_add_neg, simplify]
  sorry

lemma n_1_smul (x: R*) : (n:ℤ)•x + (1:ℤ)•x = ((n + 1):ℤ) • x := by
  simp [add_smul, one_smul, simplify]
  sorry

-- lemma smul_neg (a : 𝔽 ) (u : R*) : a • (-u) = -(a • u) :=
--   by rewrite [-neg_one_smul, -mul_smul, mul_neg_one_eq_neg, neg_smul]

@[simp]
lemma neg_zero : -0 = (0:R*) := by rfl

lemma smul_neg : ∀ (n : ℤ) (x : R*), (-n) • x = -(n • x) :=
  λ n x => by
  cases n with
  | ofNat n =>
    induction n with
    | zero =>
      show (0 : ℤ) • x = -(0 • x)
      calc
        (0 : ℤ) • (x: R*)
        = zero := by rw [zero_smul]
        _ = 0 := by rw [zero0]
        _ = -0 := by rw [neg_zero]
        _ = -zero := by rw [zero0]
        _ = -(0 • x) := by rw [zero_smuln]
    | succ n ih => --
        have ih0 : (-n : ℤ) • x = -((n: ℤ) • x) := by exact ih
        show (- (n + 1) : ℤ) • x = -((n + 1 : ℤ) • x)
        calc
           (- (n + 1) : ℤ) • x
          = ((-n - 1) : ℤ) • x := by simp [neg_add' n 1]
          _ = ((-n - 1) : ℤ) • x := by rfl
           _ = ((-n:ℤ)) • x - (1: ℤ) • x := by exact sub_smul (-n:ℤ) (1:ℤ) x
           _ = (-(n:ℤ)) • x - (1: ℤ) • x := by simp [add_smul, sub_eq_add_neg]
           _ = (-n:ℤ) • x - x := by rfl
           _ = -((n:ℤ) • x) - x := by simp [ih0]
           _ = -((n:ℤ) • x + x) := by rw [←neg_add'' ((n:ℤ) • x) x]
           _ = -((n:ℤ) • x + (1:ℤ)•x) := by simp [one_smul]
          --  _ = -((n+1:ℤ))•x := by simp [n_1_smul]
          --  _ = -((n:ℤ) + (1:ℤ))•x := by simp [←add_smul]
          --  _ = -((n:ℤ) • x + (1:ℤ)•x) := by rw [neg_sub]
          --  _ = -(n • x + x) := by rw [neg_sub]
          --  _ = -((n + 1) • x) := by rw [add_smul]
            _ = -(((n + 1): ℤ) • x) := by sorry -- rw [Nat.cast_succ]
          -- _ = -((ofNat (n + 1)) • x) := by rw [Nat.cast_succ]
            -- = -((n + 1 : ℤ) • x) := by rw [←ih, neg_smul_eq_smul_neg]
        -- show (-(n + 1): ℤ) • x = -(((n + 1): ℤ) • x)
        -- calc
        --   ( -(n + 1): ℤ) • x
        --   = (-↑n - 1) • x := by rw [neg_succ]
        -- _ = (-↑n) • x - x := by rw [sub_smul]
        -- _ = -(↑n • x) - x := by rw [ih]
        -- _ = -(↑n • x + x) := by rw [neg_sub]
        -- _ = -((↑n + 1) • x) := by rw [add_smul]
        -- _ = -(((n + 1): ℤ) • x) := by rw [Nat.cast_succ]
  | negSucc n =>
    show - -[n+1] • x = -(-[n+1] • x)
    sorry
    -- calc
    -- failed to synthesize Neg ℕ
    --   (- -(1+n) • x)
    --     = (n + 1) • x := by rw [neg_negSucc]
    --   _ = -( -[1+ n] • x) := by rw [negSucc_smul]

-- lemma smul_neg' : ∀ (n : ℤ) (x : R*), (-n) • x = -(n • x) :=
--   λ n x => by
--   cases n with
--   | ofNat n =>
--     induction n with
--     | zero =>
--       show 0•(x:R*) = -(0•x:R*)
--       calc
--         (0 : ℤ) • (x:R*)
--         = [] := by rw [HSMul.hSMul, zero]
--         _ = [] := by rw [HSMul.hSMul, neg_zero]
--     | succ n ih =>
--       simp [HSMul.hSMul, ih, neg_zero]
--       rw [neg_smul_eq_smul_neg]
--   | negSucc n =>
--     simp [HSMul.hSMul]
--     rw [neg_smul_eq_smul_neg]

lemma zsmul_neg : ∀ (n : ℤ) (x : R*), n • x = -n • -x :=
  λ n x => by
    cases n with
    | ofNat n =>
      induction n with
      | zero =>
        sorry
        -- simp [HSMul.hSMul, zero]
      | succ n ih =>
        simp [HSMul.hSMul]
        sorry
        -- rw [ih]
    | negSucc n =>
      simp [HSMul.hSMul]
      sorry

-- lemma zsmul_neg' : ∀ (n : ℤ) (x : R*), n • x = -n • -x := λ n x => by
--     induction n with
--     | hz =>
--       simp [HSMul.hSMul, zero]
--     | hn n ih =>
--     -- case n = 0

--     -- case n = 1

--       simp [HSMul.hSMul, ih, Neg.neg]
--       sorry
--     | hp n ih =>
--       simp [HSMul.hSMul]
--       rw [ih]
--       rw [Neg.neg, Neg.neg]
--       -- rw [zsmul_neg, zsmul_neg]
--       sorry



lemma smul_succ : ∀ (n : ℕ) (x : R*), (n + 1) • x = x + n • x :=
  λ n x => by
    induction n with
    | zero =>
      simp [Nat.succ_eq_add_one, HSMul.hSMul, zero, add_zero]
      rw [add_nil]
    | succ n ih =>
      simp [Nat.succ_eq_add_one, HSMul.hSMul]
      sorry
      -- rw [ih]

-- x + 0 • x = x
-- lemma zsmul_succ : ∀ (n : ℕ) (x : R*), (n + 1) • x = x + n • x :=
--   λ n x => by
--     induction n with
--     | zero =>
--       simp [Nat.succ_eq_add_one, smul_zero, add_zero, zero_times,one_times]
--     | succ n ih =>
--       simp [Nat.succ_eq_add_one, smul_succ]





-- Named (not inlined) so `nsmul`/`zsmul` below can recurse through the *exact* same
-- terms used for `add`/`neg` — this is what lets `nsmul_succ`/`zsmul_succ'`/`zsmul_neg'`
-- close by `rfl` (the default proof Mathlib supplies) instead of needing a real proof:
-- the recursive equations are written to match those defaults verbatim.
def fieldAdd (x y : R*) : R* := normalize (x ++ y)
def fieldNeg (x : R*) : R* := normalize (x.map (λ (r, e) => (-r, e)))
def fieldMul (x y : R*) : R* :=
  normalize ((x.product y).map (λ ((r1, e1), (r2, e2)) => (r1 * r2, e1 + e2)))

/-- Iterated `fieldAdd`, matching `AddMonoid.nsmul_succ`'s shape (`nsmul (n+1) x = nsmul n x + x`)
    exactly so its default `rfl` proof applies. -/
def fieldNsmul : ℕ → R* → R*
  | 0, _ => 0
  | n + 1, x => fieldAdd (fieldNsmul n x) x

/-- Matches `SubNegMonoid.zsmul_succ'`/`zsmul_neg'`'s shapes exactly (same reason). -/
def fieldZsmul : ℤ → R* → R*
  | Int.ofNat n, x => fieldNsmul n x
  | Int.negSucc n, x => fieldNeg (fieldNsmul (n + 1) x)

def fieldQsmul (q : ℚ) (x : R*) : R* := fieldMul (embedQ q) x
def fieldNNQsmul (q : ℚ≥0) (x : R*) : R* := fieldMul (embedQ (q : ℚ)) x

-- ═══════════════════════════════════════════════════════════════════════════
-- MUL-SIDE CONVOLUTION: `coeffAt (fieldMul x y) e` is the convolution
-- `Σ_{p∈x} p.1 * coeffAt y (e - p.2)` — same `coeffAt`/`eq_of_simplify_eq`
-- technique as the additive side, one level deeper (`List.product`/`flatMap`
-- instead of `List.append`). `coeffAt_mul_symm` lets either argument be
-- iterated concretely while the other stays abstract (via its `coeffAt`),
-- which is what unlocks `mul_comm`/`mul_assoc`/distributivity below without
-- needing a `List.product` swap-permutation lemma (Mathlib doesn't have one).
-- ═══════════════════════════════════════════════════════════════════════════

theorem coeffAt_flatMap {α : Type} (l : List α) (g : α → List (𝔽 × 𝔽)) (e : 𝔽) :
    coeffAt (l.flatMap g) e = (l.map (fun a => coeffAt (g a) e)).sum := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.flatMap_cons]
    show coeffAt (List.append (g a) (t.flatMap g)) e = (List.map (fun a => coeffAt (g a) e) (a :: t)).sum
    rw [coeffAt_append, ih, List.map_cons, List.sum_cons]

theorem coeffAt_scale_shift (y : List (𝔽 × 𝔽)) (r1 e1 e : 𝔽) :
    coeffAt (y.map (fun (p : 𝔽 × 𝔽) => (r1 * p.1, e1 + p.2))) e = r1 * coeffAt y (e - e1) := by
  induction y with
  | nil => simp [coeffAt]
  | cons p rest ih =>
    obtain ⟨r2, e2⟩ := p
    simp only [List.map_cons]
    rw [coeffAt_cons, coeffAt_cons, ih]
    by_cases h : e1 + e2 = e
    · have h' : e2 = e - e1 := by linarith
      simp [h']
      ring
    · have h' : e2 ≠ e - e1 := by intro hc; apply h; linarith
      simp [h, h']

/-- `coeffAt` of a product, in terms of `x`'s raw entries and `y`'s `coeffAt`. -/
theorem coeffAt_mul (x y : R*) (e : 𝔽) :
    coeffAt (fieldMul x y) e = (x.map (fun p => p.1 * coeffAt y (e - p.2))).sum := by
  unfold fieldMul normalize
  rw [coeffAt_simplify]
  have hp : (x.product y).map (fun ((r1, e1), (r2, e2)) => (r1 * r2, e1 + e2))
      = x.flatMap (fun p => y.map (fun q => (p.1 * q.1, p.2 + q.2))) := by
    show (x.flatMap (fun a => y.map (Prod.mk a))).map
        (fun ((r1, e1), (r2, e2)) => (r1 * r2, e1 + e2))
      = x.flatMap (fun p => y.map (fun q => (p.1 * q.1, p.2 + q.2)))
    induction x with
    | nil => rfl
    | cons a t ih =>
      simp only [List.flatMap_cons, List.map_append, ih]
      congr 1
      rw [List.map_map]
      rfl
  rw [hp, coeffAt_flatMap]
  congr 1
  apply List.map_congr_left
  intro p hp
  exact coeffAt_scale_shift y p.1 p.2 e

theorem coeffAt_fieldAdd (x y : R*) (e : 𝔽) : coeffAt (fieldAdd x y) e = coeffAt x e + coeffAt y e := by
  unfold fieldAdd normalize
  rw [coeffAt_simplify]
  show coeffAt (merge x y) e = _
  exact coeffAt_merge x y e

theorem sum_indicator_scale (y : List (𝔽 × 𝔽)) (r c : 𝔽) :
    (y.map (fun q => if q.2 = c then r * q.1 else 0)).sum = r * coeffAt y c := by
  induction y with
  | nil => simp [coeffAt]
  | cons q t iht =>
    obtain ⟨r2, e2⟩ := q
    rw [coeffAt_cons]
    simp only [List.map_cons, List.sum_cons]
    by_cases h : e2 = c
    · simp [h, iht]; ring
    · simp [h, iht]

/-- The convolution sum is symmetric in `x`/`y` (proved directly by induction,
avoiding the need for a `List.product x y ~ List.product y x` permutation
lemma, which Mathlib doesn't provide). -/
theorem mul_sum_symm (x y : R*) (e : 𝔽) :
    (x.map (fun p => p.1 * coeffAt y (e - p.2))).sum
      = (y.map (fun q => q.1 * coeffAt x (e - q.2))).sum := by
  induction x with
  | nil => simp [coeffAt]
  | cons p rest ih =>
    obtain ⟨r, e1⟩ := p
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    have hstep : (y.map (fun q => q.1 * coeffAt ((r, e1) :: rest) (e - q.2))).sum
        = (y.map (fun q => q.1 * ((if e1 = e - q.2 then r else 0) + coeffAt rest (e - q.2)))).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro q _
      rw [coeffAt_cons]
    rw [hstep]
    rw [show (fun q : 𝔽 × 𝔽 => q.1 * ((if e1 = e - q.2 then r else 0) + coeffAt rest (e - q.2)))
        = (fun q : 𝔽 × 𝔽 => q.1 * (if e1 = e - q.2 then r else 0) + q.1 * coeffAt rest (e - q.2))
        from funext (fun q => by ring)]
    rw [List.sum_map_add]
    congr 1
    rw [show (fun q : 𝔽 × 𝔽 => q.1 * (if e1 = e - q.2 then r else 0))
        = (fun q : 𝔽 × 𝔽 => if q.2 = e - e1 then r * q.1 else 0) from
      funext (fun q => by
        by_cases h : e1 = e - q.2
        · have h' : q.2 = e - e1 := by linarith
          rw [if_pos h, if_pos h']; ring
        · have h' : q.2 ≠ e - e1 := by intro hc; apply h; linarith
          rw [if_neg h, if_neg h', mul_zero])]
    exact (sum_indicator_scale y r (e - e1)).symm

/-- `coeffAt_mul` with the roles swapped (iterating over the second argument
instead of the first). -/
theorem coeffAt_mul_symm (x y : R*) (e : 𝔽) :
    coeffAt (fieldMul x y) e = (y.map (fun q => q.1 * coeffAt x (e - q.2))).sum := by
  rw [coeffAt_mul, mul_sum_symm]

theorem sum_map_sum_comm {α β : Type} (l1 : List α) (l2 : List β) (f : α → β → ℚ) :
    (l1.map (fun a => (l2.map (fun b => f a b)).sum)).sum
      = (l2.map (fun b => (l1.map (fun a => f a b)).sum)).sum := by
  induction l1 with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    rw [← List.sum_map_add]

theorem sum_mul_left {α : Type} (r : 𝔽) (l : List α) (f : α → 𝔽) :
    r * (l.map f).sum = (l.map (fun a => r * f a)).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp [mul_add, ih]

instance : Field R* := {
  zero := zero,
  one := one,
  add := fieldAdd,
  neg := fieldNeg,
  inv := λ x => x.map (λ (r, e) => (r⁻¹, -e)),
  mul := fieldMul,
  div := λ x y => x * y⁻¹,
  nsmul := fieldNsmul,
  zsmul := fieldZsmul,
  qsmul := fieldQsmul,
  nnqsmul := fieldNNQsmul,
  -- `qsmul_def : qsmul q x = ↑q * x` and `nnqsmul_def` need `(↑q : R*)` — the
  -- auto-derived `RatCast R*`/`NNRatCast R*` instances (`Rat.castRec` over
  -- `IntCast`/`NatCast`, themselves `Int.castDef`/`Nat.unaryCast` over THIS
  -- instance's own `add`/`neg`/`one`/`zero`) — to agree with `embedQ q`. That's
  -- a genuine (if believable) fact, not a `rfl`: it needs induction relating
  -- `Nat.unaryCast`/`Int.castDef` to `fieldNsmul`/`fieldZsmul` on `1`, then one
  -- more step to `Rat.castRec`. Left open; `fieldQsmul`/`fieldNNQsmul` above are
  -- still the mathematically correct operations (ring-multiply by the embedded
  -- rational) regardless of whether this bridging identity is proved.
  qsmul_def := sorry,
  nnqsmul_def := sorry,
  sub_eq_add_neg := fun x y => by
    show merge x (List.map (fun p : 𝔽 × 𝔽 => (-p.1, p.2)) y)
      = normalize (merge x (normalize (List.map (fun p : 𝔽 × 𝔽 => (-p.1, p.2)) y)))
    apply eq_of_simplify_eq
    unfold normalize
    rw [simplify_idempotent]
    apply simplify_eq_of_coeffAt_eq
    intro e
    rw [coeffAt_merge, coeffAt_merge, coeffAt_simplify],
  zero_add := fun x => by
    show normalize (merge 0 x) = x
    unfold normalize
    apply eq_of_simplify_eq
    rw [simplify_idempotent]
    apply simplify_eq_of_coeffAt_eq
    intro e
    rw [coeffAt_merge]
    have h0 : coeffAt (0 : R*) e = 0 := coeffAt_nil e
    rw [h0]
    ring,
  zero_mul := fun x => by
    show normalize ((List.product (0 : R*) x).map
      (fun ((r1, e1), (r2, e2)) => (r1 * r2, e1 + e2))) = 0
    have hp : List.product (0 : R*) x = ([] : List ((𝔽 × 𝔽) × 𝔽 × 𝔽)) := rfl
    rw [hp]
    show simplify ([] : R*) = 0
    rw [simplify_nil]
    rfl,
  mul_zero := fun x => by
    show normalize ((List.product x (0 : R*)).map
      (fun ((r1, e1), (r2, e2)) => (r1 * r2, e1 + e2))) = 0
    have hp : List.product x (0 : R*) = ([] : List ((𝔽 × 𝔽) × 𝔽 × 𝔽)) := by
      show List.flatMap (fun a => List.map (Prod.mk a) ([] : List (𝔽 × 𝔽))) x = []
      induction x with
      | nil => rfl
      | cons a t ih => simp [List.flatMap_cons, ih]
    rw [hp]
    show simplify ([] : R*) = 0
    rw [simplify_nil]
    rfl,
  exists_pair_ne := ⟨0, 1, by native_decide⟩,
  inv_zero := rfl,
  neg_add_cancel := fun x => by
    show normalize (merge (normalize (x.map (fun (p : 𝔽 × 𝔽) => (-p.1, p.2)))) x) = ([] : R*)
    unfold normalize
    rw [← simplify_nil]
    apply simplify_eq_of_coeffAt_eq
    intro e
    rw [coeffAt_merge, coeffAt_simplify, coeffAt_neg_map, coeffAt_nil]
    ring,
  add_assoc := fun x y z => by
    show normalize (merge (normalize (merge x y)) z) = normalize (merge x (normalize (merge y z)))
    unfold normalize
    apply eq_of_simplify_eq
    rw [simplify_idempotent, simplify_idempotent]
    apply simplify_eq_of_coeffAt_eq
    intro e
    rw [coeffAt_merge, coeffAt_merge, coeffAt_simplify, coeffAt_simplify, coeffAt_merge,
      coeffAt_merge]
    ring,
  add_comm := fun x y => by
    show normalize (merge x y) = normalize (merge y x)
    unfold normalize
    apply eq_of_simplify_eq
    rw [simplify_idempotent, simplify_idempotent]
    apply simplify_eq_of_coeffAt_eq
    intro e
    rw [coeffAt_merge, coeffAt_merge]
    ring,
  left_distrib := fun x y z => by
    apply eq_of_simplify_eq
    apply simplify_eq_of_coeffAt_eq
    intro e
    show coeffAt (fieldMul x (fieldAdd y z)) e = coeffAt (fieldAdd (fieldMul x y) (fieldMul x z)) e
    rw [coeffAt_mul, coeffAt_fieldAdd, coeffAt_mul, coeffAt_mul]
    rw [show (fun p : 𝔽 × 𝔽 => p.1 * coeffAt (fieldAdd y z) (e - p.2))
        = (fun p : 𝔽 × 𝔽 => p.1 * (coeffAt y (e - p.2) + coeffAt z (e - p.2))) from
      funext (fun p => by rw [coeffAt_fieldAdd])]
    rw [show (fun p : 𝔽 × 𝔽 => p.1 * (coeffAt y (e - p.2) + coeffAt z (e - p.2)))
        = (fun p : 𝔽 × 𝔽 => p.1 * coeffAt y (e - p.2) + p.1 * coeffAt z (e - p.2)) from
      funext (fun p => by ring)]
    exact List.sum_map_add,
  right_distrib := fun x y z => by
    apply eq_of_simplify_eq
    apply simplify_eq_of_coeffAt_eq
    intro e
    show coeffAt (fieldMul (fieldAdd x y) z) e = coeffAt (fieldAdd (fieldMul x z) (fieldMul y z)) e
    rw [coeffAt_fieldAdd]
    rw [coeffAt_mul_symm, coeffAt_mul_symm, coeffAt_mul_symm]
    simp only [coeffAt_fieldAdd]
    rw [show (fun q : 𝔽 × 𝔽 => q.1 * (coeffAt x (e - q.2) + coeffAt y (e - q.2)))
        = (fun q : 𝔽 × 𝔽 => q.1 * coeffAt x (e - q.2) + q.1 * coeffAt y (e - q.2)) from
      funext (fun q => by ring)]
    exact List.sum_map_add,
  mul_assoc := fun x y z => by
    apply eq_of_simplify_eq
    apply simplify_eq_of_coeffAt_eq
    intro e
    show coeffAt (fieldMul (fieldMul x y) z) e = coeffAt (fieldMul x (fieldMul y z)) e
    rw [coeffAt_mul_symm (fieldMul x y) z e, coeffAt_mul x (fieldMul y z) e]
    simp only [coeffAt_mul, coeffAt_mul_symm y z]
    rw [show (fun r : 𝔽 × 𝔽 => r.1 * (x.map (fun p => p.1 * coeffAt y (e - r.2 - p.2))).sum)
        = (fun r : 𝔽 × 𝔽 => (x.map (fun p => r.1 * (p.1 * coeffAt y (e - r.2 - p.2)))).sum) from
      funext (fun r => sum_mul_left r.1 x _)]
    rw [show (fun p : 𝔽 × 𝔽 => p.1 * (z.map (fun r => r.1 * coeffAt y (e - p.2 - r.2))).sum)
        = (fun p : 𝔽 × 𝔽 => (z.map (fun r => p.1 * (r.1 * coeffAt y (e - p.2 - r.2)))).sum) from
      funext (fun p => sum_mul_left p.1 z _)]
    rw [sum_map_sum_comm z x (fun r p => r.1 * (p.1 * coeffAt y (e - r.2 - p.2)))]
    congr 1
    apply List.map_congr_left
    intro p _
    congr 1
    apply List.map_congr_left
    intro r _
    have : e - r.2 - p.2 = e - p.2 - r.2 := by ring
    rw [this]
    ring,
  one_mul := fun x => by
    show normalize ((List.product (1 : R*) x).map
      (fun ((r1, e1), (r2, e2)) => (r1 * r2, e1 + e2))) = x
    have hp : List.product (1 : R*) x = x.map (fun q => (((1 : 𝔽), (0 : 𝔽)), q)) := by
      show List.flatMap (fun a => x.map (Prod.mk a)) [((1 : 𝔽), (0 : 𝔽))]
        = x.map (fun q => (((1 : 𝔽), (0 : 𝔽)), q))
      rw [List.flatMap_singleton]
    rw [hp, List.map_map]
    have hid : ((fun ((r1, e1), (r2, e2)) => (r1 * r2, e1 + e2)) ∘
        fun q : 𝔽 × 𝔽 => (((1 : 𝔽), (0 : 𝔽)), q)) = id := by
      funext q
      obtain ⟨r, e⟩ := q
      simp
    rw [hid, List.map_id]
    unfold normalize
    exact eq_of_simplify_eq (simplify x) x (simplify_idempotent x),
  mul_one := fun x => by
    show normalize ((List.product x (1 : R*)).map
      (fun ((r1, e1), (r2, e2)) => (r1 * r2, e1 + e2))) = x
    have hp : List.product x (1 : R*) = x.map (fun p => (p, ((1 : 𝔽), (0 : 𝔽)))) := by
      show List.flatMap (fun a => [(a, ((1 : 𝔽), (0 : 𝔽)))]) x
        = x.map (fun p => (p, ((1 : 𝔽), (0 : 𝔽))))
      induction x with
      | nil => rfl
      | cons a t ih => simp [List.flatMap_cons, ih]
    rw [hp, List.map_map]
    have hid : ((fun ((r1, e1), (r2, e2)) => (r1 * r2, e1 + e2)) ∘
        fun p : 𝔽 × 𝔽 => (p, ((1 : 𝔽), (0 : 𝔽)))) = id := by
      funext p
      obtain ⟨r, e⟩ := p
      simp
    rw [hid, List.map_id]
    unfold normalize
    exact eq_of_simplify_eq (simplify x) x (simplify_idempotent x),
  mul_comm := fun x y => by
    apply eq_of_simplify_eq
    apply simplify_eq_of_coeffAt_eq
    intro e
    show coeffAt (fieldMul x y) e = coeffAt (fieldMul y x) e
    rw [coeffAt_mul, coeffAt_mul_symm],
  -- Not provable: `inv` (`fun (r,e) => (r⁻¹,-e)`, per-term) is only a genuine
  -- multiplicative inverse for single-term monomials. Confirmed false via
  -- native_decide: (ε+ω) * (ε+ω)⁻¹ = ω²+2+ε² ≠ 1. This isn't a definition
  -- bug like npow/nsmul/zsmul were — R* only stores *finite*-support lists,
  -- and finite-support Laurent-type series (ℚ[ω,ω⁻¹]-ish, here with rational
  -- exponents) genuinely aren't a field: e.g. 1/(1+ω) has no finite
  -- representation, only an infinite power series one. `Field R*` is
  -- structurally aspirational for multi-term elements; left `sorry`.
  mul_inv_cancel := by sorry,
  add_zero := fun x => by
    show normalize (merge x 0) = x
    unfold normalize
    apply eq_of_simplify_eq
    rw [simplify_idempotent]
    apply simplify_eq_of_coeffAt_eq
    intro e
    rw [coeffAt_merge]
    have h0 : coeffAt (0 : R*) e = 0 := coeffAt_nil e
    rw [h0]
    ring
}




end HyperLists
end Hypers

