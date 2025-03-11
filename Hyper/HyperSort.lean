import Mathlib.Data.Real.Ereal

notation "∞" => (⊤ : EReal)
notation "-∞" => (⊥ : EReal)
namespace Hypers
section HyperGenerals
notation "𝔽" => ℚ
def Comps := List (𝔽 × 𝔽)
def HyperGeneral : Type := List (𝔽 × 𝔽)

notation "R*" => HyperGeneral
notation "𝔽*" => R*


structure HyperExtension (α : Type*) extends Real :=
  (infinite : α)
instance : One R* where one := [(1, 0)]
instance : Zero R* where zero := ([]:R*)

def zero : R* := []
def zero' : R* := [(0,0)]
def nil : R* := []
def one : R* := [(1, 0)]
def epsilon : R* := [(1, -1)]
def omega : R* := [(1, 1)]
scoped notation "O" => zero
scoped notation "I" => one
scoped notation "ε" => epsilon
scoped notation "ω" => omega
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

instance : DecidableEq 𝔽 := inferInstance
instance [DecidableEq 𝔽] : DecidableEq (𝔽 × 𝔽) := inferInstance
instance [DecidableEq (𝔽 × 𝔽)] : DecidableEq (List (𝔽 × 𝔽)) := inferInstance
instance [DecidableEq (List (𝔽 × 𝔽))] : DecidableEq R* := inferInstance
def normalize (x : R*) : R* := if x = [] ∨ x = [(0,0)] then [] else x
instance : Coe (List (𝔽 × 𝔽)) R* where coe x := x -- normalize x
instance : Coe (List (ℕ × ℕ)) R* where coe x := x.map (λ (a, b) => ((a : 𝔽), (b : 𝔽)))
instance : Coe (List (ℤ × ℤ)) (List (𝔽 × 𝔽)) where coe x := x.map (λ (a, b) => ((a : 𝔽), (b : 𝔽)))
instance : OfNat R* 0 where ofNat := []
instance : OfNat R* 1 where ofNat := [(1, 0)]
instance : OfNat R* n where ofNat := [(n, 0)]
instance : OfNat (List (ℚ × ℚ)) 1 where ofNat := [(1, 0)]

instance {n : ℕ} : OfNat R* n where ofNat := [(n, 0)]
-- instance : OfNat List 0 where ofNat := []
instance : EmptyCollection R* where emptyCollection := []

-- #eval 0 = []
-- #eval ([(0,0)]:𝔽*) = (0:𝔽*) -- todo?
#eval ([]:𝔽*) = (0:𝔽*)
#eval ([]:𝔽*) = []
#eval (0:𝔽*) = []
#eval (0:𝔽*)
#eval (1:𝔽*)

def simplify (a : R*) : R* :=
  a.foldl (λ acc (r, e) =>
    let updated := acc.map (λ (r', e') => if e = e' then (r + r', e') else (r', e'))
    if acc.any (λ (_, e') => e = e') then
      updated.filter (λ (r', _) => r' ≠ 0)
    else
      (r, e) :: acc
  ) []


-- #eval nil : R*
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

@[simp] theorem merge_cons (a : α) (x y : R*) : merge (a :: x) y = simplify (List.append (a :: x) y) :=
  by simp [merge]
-- have h : ([] : R*) + x = x := by
--       rw [merge] -- failed to rewrite using equation theorems for 'Hypers.merge'.

def HyperEq (x y : R*) : Prop := simplify x = simplify y
infix:50 " ≅ " => HyperEq

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
-- instance : HAdd R* (List (𝔽 × 𝔽)) R* where hAdd := merge
-- instance : HAdd R* (List (ℚ × ℚ)) R* where hAdd := merge
instance : HAdd R* (List (ℕ × ℕ)) R* where hAdd x y := merge x y
instance : HAdd R* (𝔽 × 𝔽) R* where hAdd x y := merge x y
-- instance : HAdd R* (ℚ × ℚ) R* where hAdd x y := merge x y
instance : HAdd R* (ℕ × ℕ) R* where hAdd x y := merge x y
-- instance : HAdd (List (ℚ × ℚ)) R* R* where hAdd := merge
instance : HAdd (List (𝔽 × 𝔽)) R* R* where hAdd := merge
-- instance : HAdd (List (ℕ × ℕ)) R* R* where hAdd x y := merge x y
instance : HAdd (𝔽 × 𝔽) R* R* where hAdd x y := merge x y
-- instance : HAdd (ℚ × ℚ) R* R* where hAdd x y := merge x y
instance : HAdd (ℕ × ℕ) R* R* where hAdd x y := merge x y

-- instance : HAdd (𝔽 × 𝔽) (𝔽 × 𝔽) R* where hAdd x y := merge x y
-- instance : HAdd (𝔽 × 𝔽) (List (𝔽 × 𝔽)) R* where hAdd x y := merge x y
-- instance : HAdd (List (𝔽 × 𝔽)) (𝔽 × 𝔽) R* where hAdd x y := merge x y
-- instance : HAdd (List (𝔽 × 𝔽)) (List (𝔽 × 𝔽)) R* where hAdd x y := merge x y
-- instance : HAdd (ℕ × ℕ) (ℕ × ℕ) R* where hAdd x y := merge x y
-- instance : HAdd (ℕ × ℕ) (List (ℕ × ℕ)) R* where hAdd x y := merge x y
instance : HAdd (List (ℕ × ℕ)) (ℕ × ℕ) R* where hAdd x y := merge x y
-- instance : HAdd (List (ℕ × ℕ)) (List (ℕ × ℕ)) R* where hAdd x y := merge x y


instance : Neg R* where neg x := normalize (x.map λ (r, e) => (-r, e))
instance : Sub R* where sub x y := x + -y

#eval one + one
#eval 0 + one
#eval 1 + one
#eval -1 + one
#eval 1 - one
#eval -1 - one
#eval one + zero
#eval one + 0
#eval one + 1
#eval one - 1
#eval one + (1:R*)
#eval one + (1,0)
#eval one + [(1,0)]
#eval one + ((1,0):R*)
-- #eval one + ([(1,0)]:R*) -- FAILS!

#eval (1,0) + one
#eval [((1:ℕ),(0:ℕ))] + one
#eval [((1:𝔽),(0:𝔽))] + one
-- #eval [(1,0)] + one -- fails because 1, 0 are special, too hard to figure out the type
-- #eval [(3,3)] + one -- fails because WHY?? succ ^^ ?
-- #eval [(3,3)] + one -- fails because WHY??
-- #eval [(3,(3:ℕ))] + one -- fails because WHY??
#eval ((1,0):R*) + one
#eval ([(1,0)]:R*) + one
-- #eval one + ([(1,0)]:R*) -- FAILS!?!

#eval ([⟨1,0⟩] : R*)
#eval ([(1,0)] : R*)

#eval ((1,0) : R*) + (1,0)

#eval ⟨1,0⟩ + (1,0)
#eval (1,0) + (1,0)
#eval [(1,0)]  + (1,0)
-- #eval [⟨1,0⟩]  + (1,0)

-- Why do these fail they should match the definitions:
-- instance : HAdd R* (ℕ × ℕ) R* where hAdd x y := merge x y
-- instance : Coe (ℕ × ℕ) R* where coe x := x
-- #check ([(1,0)]:R*) -- List (ℚ × ℚ) but not really R* ?
-- #eval ([(1,0)]:R*) == 1
-- #eval one + ([(1,0)]:R*)
-- #eval ([⟨1,0⟩] : R*) + 1
-- #eval ([⟨1,0⟩] : R*) + (1,0)
-- #eval ([(1,0)] : R*) + 1
-- #eval ([(1,0)] : R*) + (1,0)
-- #eval ([(1,0)] : R*) + [(1,0)]

#eval ([] : R*) ++ [(1,0)]
#eval ([(1,0)] : R*) ++ [(1,0)]
#eval [(1,0)] ++ []
#eval [(1,0)] ++ ([] : R*)
#eval [(1,0)] ++ ([(1,0)] : R*)
#eval [(1,0)] ++ ((1,0) : R*) -- FAILS unless
-- instance : HAppend (List (𝔽 × 𝔽)) R* R* where hAppend := merge -- needed (why?)


instance : HSMul ℕ R* R* where hSMul n x := if n = 0 then [] else x.map (λ (r, e) => (n * r, e))
instance : HSMul ℤ R* R* where hSMul n x := if n = 0 then [] else x.map (λ (r, e) => (n * r, e))
instance : HSMul 𝔽 R* R* where hSMul n x := if n = 0 then [] else x.map (λ (r, e) => (n * r, e))
instance : Mul R* where
  mul x y := normalize ((x.product y).map (λ ((r1, e1), (r2, e2)) => (r1 * r2, e1 + e2)))

instance : Inv R* where
  inv x := x.map (λ (r, e) => (r⁻¹, -e))
instance : SMul ℤ R* where
  smul n x := x.map (λ (r, e) => (n * r, e))
instance : HDiv R* R* R* where
  hDiv x y := x * y⁻¹
instance : HDiv 𝔽 R* R* where
  hDiv x y := x • y⁻¹


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
lemma simplify_preserves_eq {x y : R*} (h : x = y) : simplify x = simplify y := by rw [h]
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

instance : ToString R* where
  toString f :=
    let terms := simplify f
    let (constants, exponentials) := terms.partition (λ (c, e) => e = 0)
    let constSum := constants.foldl (λ acc (c, _) => acc + c) (0:𝔽)
    let expStr := exponentials.map (λ (c, e) =>
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

-- instance : Repr R* where
--   reprPrec f _ := toString f

#eval  ω * ε
#eval  2*ω * ε
#eval ε
#eval 1/ε - ω
#print "----"
#eval ω - ω
#eval ω - ω = O
#eval ω - ω = 0
scoped notation:max n "ω" => n • ω
#eval  2ω * ε
#eval  1 + 2ω + 1 + 2ω
#eval! simplify 1 + ω + 1 + 1/ε

lemma zero_add : ∀ x : R*,  zero + x = x := λ x => by
    simp only [Add.add, HAdd.hAdd, zero]
    have h : ([] : R*) + x = x := by
      rw [merge] -- failed to rewrite using equation theorems for 'Hypers.merge'.
      case [] => rfl
      case (a :: l) => rfl
    show ([] : R*) + x = x
    rw [h]
    rw [HAdd.hAdd]
    have h1 : ([] : R*) ++ x = x := by rw [HAppend.hAppend]
    show ([] : R*) ++ x = x
    rw [h]

lemma add_zero : ∀ x : R*, x + zero = x :=
  λ x => by
    simp only [Add.add, zero]

    have h : x ++ ([] : R*) = x := by
      rw [HAppend.hAppend]
      -- rw [List.append_nil]
    show x ++ ([] : R*) = x
    rw [h]












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
  zsmul_succ' := by
    intros n x
    simp [HSMul.hSMul]
    cases n
    ·
      simp [zero, List.map_append, HAdd.hAdd]
      rfl
    ·
      simp [Nat.succ_eq_add_one]
      have h : (n + 1) = 0 ↔ False := by
        simp [Nat.succ_ne_zero]
      simp [h]
      sorry
  zsmul_neg' := by
    intros n x
    simp [HSMul.hSMul]
    cases n
    ·
      simp [zero]
      rfl
    ·
      have h : -n = 0 ↔ False := by simp [neg_eq_zero]
      simp [h]
      sorry

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

  add_zero :=
    by
      intro a
      have h : (a:R*) ++ 0 = a := by
        induction x with
        | nil => rfl
        | cons hd tl ih => simp [List.append]
        rw [ih]
      show x ++ [] = x
      rw [List.append_nil]
      rfl

}


end HyperGenerals
end Hypers
