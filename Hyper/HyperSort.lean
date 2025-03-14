import Mathlib.Data.Real.Ereal
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

instance : Coe 𝔽 𝔽* where coe (n:𝔽) : R* := [(n, 0)]
instance : Coe ℕ 𝔽* where coe (n:ℕ) : R* := [((n:𝔽), 0)]
instance : Coe ℚ 𝔽* where coe (q:ℚ) : R* := [(q, 0)]
instance : Coe ℤ 𝔽* where coe (q:ℤ) : R* := [(q, 0)]
instance : Coe (ℚ×ℚ) 𝔽* where coe (q:ℚ×ℚ) : R* := (q.1, q.2) :: []
instance : Coe (𝔽×𝔽) 𝔽* where coe (q:𝔽×𝔽) : R* := (q.1, q.2) :: []
instance : Coe (ℕ × ℕ) 𝔽* where coe (q: ℕ×ℕ) : R* := (q.1, q.2) :: []
instance : Coe (ℤ × ℤ) 𝔽* where coe (q: ℤ×ℤ) : R* := (q.1, q.2) :: []
instance : Coe (ℕ × ℕ) (𝔽 × 𝔽) where coe (q: ℕ×ℕ) : (𝔽 × 𝔽) := ((q.1:𝔽), (q.2:𝔽))
instance : Coe (ℤ × ℤ) (𝔽 × 𝔽) where coe (q: ℤ×ℤ) : (𝔽 × 𝔽) := ((q.1:𝔽), (q.2:𝔽))
instance : Coe (ℕ × ℕ) R* where coe x := [x]
-- UN-SIMPLIFIED!
instance : Coe (List (𝔽 × 𝔽)) R* where coe x := x -- simplify x
instance : Coe (List (ℕ × ℕ)) R* where coe x := x.map (λ (a, b) => ((a : 𝔽), (b : 𝔽)))
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


def simplify (a : R*) : R* :=
  a.foldl (λ acc (r, e) =>
    let updated := acc.map (λ (r', e') => if e = e' then (r + r', e') else (r', e'))
    if acc.any (λ (_, e') => e = e') then
      updated.filter (λ (r', _) => r' ≠ 0)
    else
      (r, e) :: acc
  ) [] |>.filter (λ (r, _) => r ≠ 0) -- remove all zero coefficients (0,*)

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


-- @[simp]
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
-- instance : HasEquiv R* where Equiv := HyperEq
instance : HasEquiv R* where Equiv x y := simplify x == simplify y
infix:50 " ≅ " => HyperEq  -- NOT NEEDED, we have the standard ≈ ≠ ~ !!!

#eval ([(0,0)] : R*) ≈ (0: R*) -- true now FALSE AGAIN?????
#eval ([(0,0)] : R*) = (0: R*) -- always false! (OK)

-- Adding additional evaluation to check equality with simplified forms
-- #eval ([(0,0)] : R*) ≅ (0: R*)

instance HyperSetoid : Setoid R* :=
{ r := HyperEq,
  iseqv := ⟨
    (by intro x; rfl),
    (by intro x y h; unfold HyperEq at h ⊢; rw [h]),
    (by intro x y z hxy hyz; unfold HyperEq at hxy hyz ⊢; rw [hxy, hyz])
  ⟩ }
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





instance : Field R* := {
  zero := zero,
  one := one,
  add := λ x y => normalize (x ++ y),
  neg := λ x => normalize (x.map (λ (r, e) => (-r, e))),
  inv := λ x => x.map (λ (r, e) => (r⁻¹, -e)),
  mul := λ x y => normalize ((x.product y).map (λ ((r1, e1), (r2, e2)) => (r1 * r2, e1 + e2))),
  div := λ x y => x * y⁻¹,
  npow := λ n x => x.map (λ (r, e) => (r^n, e*n)),
  nsmul := λ n x => x.map (λ (r, e) => (n * r, e)),
  qsmul := λ q x => x.map (λ (r, e) => (q * r, e)),
  nnqsmul := λ q x => x.map (λ (r, e) => (q * r, e)),

  zsmul := λ n x => if n = 0 then [] else x.map (λ (r, e) => (n * r, e)),
  zsmul_zero' := by
    intro x
    simp [HSMul.hSMul, zero]
    rfl
  sub_eq_add_neg := sorry,
  zsmul_succ' := sorry, -- by exact zsmul_succ,
  zsmul_neg' := sorry, -- by exact zsmul_neg',
  zero_add := sorry,
  zero_mul := sorry,
  mul_zero:=sorry,
  exists_pair_ne := sorry,
  inv_zero:=sorry,
  neg_add_cancel:=sorry,
  nsmul_zero:= sorry,
  nsmul_succ:=sorry,
  npow_zero:=sorry,
  npow_succ:=sorry,
  nnqsmul_def:=sorry,
  qsmul_def:=sorry,
  add_assoc := by sorry,
  add_comm := by sorry,
  left_distrib := by sorry,
  right_distrib := by sorry,
  mul_assoc := by sorry,
  one_mul := by sorry,
  mul_one := by sorry,
  mul_comm := by sorry,
  mul_inv_cancel := by sorry,
  add_zero := by sorry
}
end HyperLists
end Hypers
