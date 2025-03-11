-- import Init.Prelude
-- import Init.Data.Nat.Basic
-- import Init.Control.Basic -- Import basic control structures in LEAN 4
-- import Mathlib.Data.Real.Basic -- Import basic real number theory in LEAN 4
import Mathlib.Data.Real.Ereal -- ∞  OR :
-- import Mathlib.Data.Real.Hyperreal -- defined as hyperfilter germ

-- set_option diagnostics true


-- def Hyperreal : Type := Germ (hyperfilter ℕ : Filter ℕ) ℝ deriving Inhabited
notation "∞" => (⊤ : EReal)
notation "-∞" => (⊥ : EReal)

-- scoped notation "ε" => epsilon
-- scoped notation "ω" => omega

namespace Hypers
section HyperGenerals

-- Avoid Real Numbers When Possible:
-- If the use of real numbers introduces complexity due to issues like non-decidability of equality, consider if your application can tolerate using rational numbers or fixed-point arithmetic, which do not have these issues in Lean.
notation "𝔽" => ℚ -- our field, true alias
-- def 𝔽 := ℚ -- treats it as own Type!!
-- variable {𝔽 : Type*} [field 𝔽] -- “Let 𝔽 be a field.”

def Comps := List (𝔽 × 𝔽)
-- def Comps := List (ℝ × ℝ)
-- def Comps := List (ℝ × ℚ) -- what about ε^π :) seriously, needed in e^πi = -1
-- def Comps := List (ℝ × ℤ) -- ℤ for exponents integer powers of ε and ω enough for now
-- def Comps := List (ℚ × ℚ)  -- but what about π?

def HyperGeneral : Type := List (𝔽 × 𝔽)

-- structure HyperGeneral :=
  -- components : List (𝔽 × 𝔽)
-- instance : Setoid HyperGeneral :=
-- { r := HyperEq, -- Use `≅` as the equivalence relation
--   iseqv := ⟨Equivalence.refl, Equivalence.symm, Equivalence.trans⟩ }
-- def HyperReal := Quotient (Setoid HyperGeneral)

-- notation "R*" => HyperReal
notation "R*" => HyperGeneral
-- notation "ℚ*" => R* -- but what about π?
notation "𝔽*" => R*
notation "𝔽⋆" => R*
-- notation "ℝ⋆" => R* -- may conflict with Hyper from Hyper.lean
-- notation "ℝ*" => R* -- may conflict with Lean 4 notation for hyperreals

-- def Hyper:= R* -- remove!

  -- components : 𝔽 → 𝔽 -- as Function, see HyperFun
  -- components : List (ℝ × ℝ) -- allow π√ε
  -- components : List (ℚ × ℚ) -- allow π√ε approximation for now
  -- components : List (Float × Float) -- allow π√ε approximation for now
  -- components : List (ℝ × ℤ) -- [(3, 0), (1, 1), (2, -2)] => 3 + ω + 2ε^2 -- note ε = ω⁻¹
  -- components : ℤ → ℝ  -- generalized for infinite lists of components
  -- components : Comps -- with indirection we can't use add := λ x y => x ++ … why?

-- structure HyperSimple :=
  -- components : ℝ × ℤ  -- ONE of (3, 0), (1, 1), (2, -2) … => 3 or ω or 2ε^2 -- note ε = ω⁻¹
  -- components : ℝ × ℝ  -- ONE of (3, 0), (1, 1), (2, -2) … => 3 or ω or 2ε^2 -- note ε = ω⁻¹

structure HyperExtension (α : Type*) extends Real :=
  (infinite : α)


instance : One R* where
  one := [(1, 0)]

instance : Zero R* where
  zero := []

-- instance : Inhabited R* := inferInstance
#eval (0:𝔽*) -- [] OK
#eval (1:𝔽*) -- [(1, 0)] OK

def zero : R* := []
def one : R* := [(1, 0)]
def epsilon : R* := [(1, -1)]
def omega : R* := [(1, 1)]

-- scoped notation "0" => zero -- doesn't work "invalid atom" also NOT NEEDED! use 0 or 0 : 𝔽*
scoped notation "O" => zero
scoped notation "I" => one
scoped notation "ε" => epsilon
scoped notation "ω" => omega

instance : Coe ℕ 𝔽* where
  coe (n:ℕ) : R* := [((n:𝔽), 0)]

instance {n : ℕ} : OfNat R* n where
  ofNat := [(n, 0)]

instance : Coe ℚ 𝔽* where
  coe (q:ℚ) : R* := [(q, 0)]

instance : Coe (ℚ×ℚ) 𝔽* where
  coe (q:ℚ×ℚ) : R* := (q.1, q.2) :: []

instance : Coe (𝔽×𝔽) 𝔽* where
  coe (q:𝔽×𝔽) : R* := (q.1, q.2) :: []

instance : Coe (List (𝔽 × 𝔽)) R* where
  coe := id

instance : HAppend R* R* R* where
  hAppend := List.append


instance : HAppend R* Comps R* where
  hAppend := List.append


def simplify (a : R*) : R* :=
  a.foldl (λ acc (r, e) =>
    let updated := acc.map (λ (r', e') => if e = e' then (r + r', e') else (r', e'))
    if acc.any (λ (_, e') => e = e') then
      updated.filter (λ (r', _) => r' ≠ 0)
    else
      (r, e) :: acc
  ) []

def HyperEq (x y : R*) : Prop := simplify x = simplify y

-- notation x " ≅ " y => HyperEq x y  -- ≃ equal after simplification
infix:50 " ≅ " => HyperEq



instance : Add R* where
  add x y := x ++ y -- unordered list :(

instance : Neg R* where
  neg x := x.map λ (r, e) => (-r, e)
  -- neg x := x.map λ ⟨r, e⟩ => (-r, e) -- !! Elements in the list can be denoted as ⟨r, e⟩ OR (r,e) real+exponents


instance : Sub R* where sub x y := x + -y

-- scalar multiplication r • a
-- instance : HSMul ℕ R* R* where
--   hSMul n x := if n = 0 then [] else x.map (λ (r, e) => (n * r, e))

-- instance : HSMul ℤ R* R* where
--   hSMul n x := if n = 0 then [] else x.map (λ (r, e) => (n * r, e))

instance : HSMul 𝔽 R* R* where
  hSMul r a := simplify (a.map (λ ⟨s, e⟩  => ((r * s), e)))


instance : HSMul ℕ R* R* where
  hSMul r a := (a.map (λ ⟨s, e ⟩ => ((r * s), e)))

-- instance : Mul 𝔽 R* where
--   mul r a := r • a

instance : Mul R* where
  mul x y := (x.product y).map (λ ((r1, e1), (r2, e2)) => (r1 * r2, e1 + e2))
  -- mul x y := (x.product y).map (λ ⟨⟨r1, e1⟩, ⟨r2, e2⟩⟩ => (r1 * r2, e1 + e2))

instance : Inv R* where
  inv x := x.map (λ (r, e) => (r⁻¹, -e))

instance : SMul ℤ R* where
  smul n x := x.map (λ (r, e) => (n * r, e))

instance : HDiv R* R* R* where
  hDiv x y := x * y⁻¹

instance : HDiv 𝔽 R* R* where
  hDiv x y := x • y⁻¹
  -- hDiv x y := (x:R*) * y⁻¹
  -- hDiv x y := if x = 0 then [] else x • y⁻¹


-- class HyperEqClass (x y : R*) : Prop := (eqv : simplify x = simplify y)
instance : Reflexive HyperEq := by
  intro x
  rfl

instance : Symmetric HyperEq := by
  intro x y h
  unfold HyperEq at h  -- Expands `HyperEq` into `simplify x = simplify y`
  unfold HyperEq       -- Expands `HyperEq` in the goal (`y ≅ x` → `simplify y = simplify x`)
  rw [h]               -- Now `rw` applies correctly

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

instance [DecidableEq 𝔽] : DecidableEq (𝔽 × 𝔽) := inferInstance
instance : DecidableEq 𝔽 := inferInstance  -- If `𝔽` already has one

-- instance  [DecidableEq Comps] : DecidableEq R* :=
--   λ x y =>
--     match decEq x y  with
--     | isTrue h  => isTrue h
--     | isFalse h => isFalse h

lemma simplify_preserves_eq {x y : R*} (h : x = y) : simplify x = simplify y := by rw [h]
-- lemma simplify_eq_implies_eq {x y : R*} (h : simplify x = simplify y) : x = y := by
--   apply Equivalence.trans
--   apply Equivalence.symm
--   exact h

-- trick to make ≅ into real equality = for proofs
instance HyperSetoid : Setoid R* :=
{ r := HyperEq,
  iseqv := ⟨
    (by intro x; rfl),  -- Reflexivity
    (by intro x y h; unfold HyperEq at h ⊢; rw [h]),  -- Symmetry
    (by intro x y z hxy hyz; unfold HyperEq at hxy hyz ⊢; rw [hxy, hyz])  -- Transitivity
  ⟩ }

def HyperQuotient := Quotient HyperSetoid
-- def HyperQuotient := Quotient R*

instance : DecidableEq ℚ := inferInstance
instance : DecidableEq 𝔽 := inferInstance
instance [DecidableEq 𝔽] : DecidableEq (𝔽 × 𝔽) := inferInstance
instance [DecidableEq (𝔽 × 𝔽)] : DecidableEq (List (𝔽 × 𝔽)) := inferInstance

instance [DecidableEq (List (𝔽 × 𝔽))] : DecidableEq R* :=
  inferInstance  -- Uses Lean's built-in instance resolution

instance [DecidableEq Comps] : DecidableEq HyperQuotient :=
  λ x y =>
    Quotient.recOnSubsingleton₂ x y (λ x y =>
      match decEq (simplify x) (simplify y) with
      | isTrue h  => isTrue (Quotient.sound h)  -- Lift `simplify x = simplify y` to `⟦x⟧ = ⟦y⟧`
      | isFalse h => isFalse (by
          intro contra
          apply h
          exact Quotient.exact contra  -- Convert `⟦x⟧ = ⟦y⟧` to `simplify x = simplify y`
        )
    )


-- instance : ToString R* where
  -- toString f := simplify f |>.toString

instance : ToString R* where
  toString f :=
    let terms := simplify f
    let (constants, exponentials) := terms.partition (λ (c, e) => e = 0)
    let constSum := constants.foldl (λ acc (c, _) => acc + c) (0:𝔽)  -- Sum up constants
    let expStr := exponentials.map (λ (c, e) =>
      if c = 1 then
        if e = 1 then "ω"
        else if e = 2 then "ω²"
        else if e = -1 then "ε"
        else if e = -2 then "ε²"
        else if e > 1 then s!"ω^{e}"
        else if e < -1 then s!"ε^{e}"
        else ""
      else
      if e = 1 then s!"{c}ω"
      else if e = 2 then s!"{c}ω²"
      else if e = -1 then s!"{c}ε"
      else if e = -2 then s!"{c}ε²"
      else if e > 1 then s!"{c}ω^{e}"
      else if e < -1 then s!"{c}ε^{e}"
      else s!""
    ) |>.intersperse " + " --
      |>.foldl String.append ""
    match (constSum, expStr) with
    | (0, exp) => exp
    | (c, "") => toString c
    | (c, exp) => s!"{c} + {exp}"

instance : Repr R* where
  reprPrec f _ := toString f
  -- reprPrec f _ := simplify f

-- Further eval examples for testing the `simplify` function
#eval  ω * ε -- [(1, 0)] OK
#eval  2*ω * ε -- [(1, 0)] OK
#eval ε
#eval 1/ε - ω
#print "----"
#eval ω - ω
#eval ω - ω = 0

scoped notation:max n "ω" => n • ω
#eval  2ω * ε -- [(2, 0)] OK
#eval  1 + 2ω + 1 + 2ω -- ≈ ([1,0],[2,1],[1,0],[2,1]]) => ([2,0],[4,1)) ≈ 2 + 4ω
#eval! simplify 1 + ω + 1 + 1/ε -- 2 + 2ω -- simplify implicit via Repr / ToString
-- nice for output but not for proofs!!!

-- lemma zsmul_zero' : ∀ x : R*, 0 • x ≅ zero :=
--   λ x => by
--     simp only [HSMul.hSMul, List.map]
--     apply Setoid.refl -- HyperEq.refl


instance : Field R* := {
  zero := zero,
  one := one,
  add := λ x y => x ++ y,
  neg := λ x => x.map (λ (r, e) => (-r, e)),
  inv := λ x => x.map (λ (r, e) => (r⁻¹, -e)),
  mul := λ x y => (x.product y).map (λ ((r1, e1), (r2, e2)) => (r1 * r2, e1 + e2)),
  div := λ x y => x * y⁻¹,
  npow := λ n x => x.map (λ (r, e) => (r^n, e*n)),
  nsmul := λ n x => x.map (λ (r, e) => (n * r, e)),
  qsmul := λ q x => x.map (λ (r, e) => (q * r, e)),
  nnqsmul := λ q x => x.map (λ (r, e) => (q * r, e)),
  zsmul := λ n x => x.map (λ (r, e) => (n * r, e)),

  zsmul_zero' := by
    show ∀ x : R*, 0 • x = zero
    intro x
    rw [HSMul.hSMul]
    simp,
  zsmul_succ' := by
    intros n x
    rw [List.map_cons]
    simp,
  zsmul_neg' := by
    intros n x
    rw [List.map_neg]
    simp,
  -- gsmul := λ n x => x.map (λ r, e => (n * r, e)),
  add_assoc := by
    intros a b c
    have h : (a ++ b) ++ c = a ++ (b ++ c) :=
      List.append_assoc a b c
    exact congrArg HyperGeneral.mk h
  zero_add := by
    intros a
    rfl,
  add_zero := by
    intros a
    have h: (0:R*) =  []  := sorry
    have h1: a ++ [] = a := List.append_nil a
    rw [h, h1]
    rfl
  add_comm := by
    intros a b
    rw [List.append_comm]
    rfl,
  -- add_left_neg := by
  --   intros a
  --   simp only [List.map_map]
  --   -- Simplification would require a proper grouping function.
  --   sorry,
  mul_assoc := by
    intros a b c
    rw [List.product_assoc]
    rfl,
  one_mul := by
    intros a
    rw [List.product_one_left]
    rfl,
  mul_one := by
    intros a
    rw [List.product_one_right]
    rfl,
  left_distrib := by
    intros a b c
    simp only [List.product_distrib_left]
    rfl,
  right_distrib := by
    intros a b c
    simp only [List.product_distrib_right]
    rfl,
  mul_comm := by
    intros a b
    rw [List.product_comm]
    rfl,
  mul_inv_cancel := by
    intros a ha
    -- Need to define a simplification that cancels inverses in our structure.
    sorry,
  -- inv_mul_cancel := by
  --   intros a ha
  --   -- Same issue as above, requires simplification function.
  --   sorry,
  -- zero_ne_one := by
  --   intro h
  --   -- This would require proving that `[] ≠ [(1,0)]` which is trivial but needs explicit `List` reasoning.
  --   sorry

--   -- include proofs showing these satisfy field axioms
--   zero_add := sorry,
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
  -- zsmul_def:=sorry,
  -- zsmul_zero:=sorry,
  -- by
  --   intros x
  --   rw [List.append_nil]
  --   rfl,
  -- nsmul_zero1 := by
  --   intros x
  --   rw [List.map_nil, List.nil_append]
  --   rfl,
--   add_assoc := sorry,
--   add_zero := sorry,
--   add_comm:=sorry,
--   -- add_left_neg:=sorry,
--   left_distrib:=sorry,
--   right_distrib:=sorry,
--   one_mul:=sorry,
--   mul_assoc:=sorry,
--   mul_one:=sorry,
--   mul_inv_cancel:=sorry,
--   mul_comm:=sorry,
--   zsmul:=sorry,

  -- zsmul_zero:=sorry,
  -- zsmul_succ:=sorry,
  -- gsmul := sorry,
  -- nsmul:=sorry,
-- by
--   intros n x
--   rw [List.map_map]
--   simplify,
  -- npow_succ:=sorry,
  -- npow_zero:=sorry,
  -- nsmul_succ:=sorry,
  -- zsmul_neg:=sorry,
  -- zsmul_zero:=sorry,
  -- zsmul_succ:=sorry,
  -- gsmul := sorry,
--   nsmul:=sorry,
}


  -- inv_zero:= sorry,
  -- zero_add := λ x => sorry,
  -- zero_mul := λ x => sorry,
  -- add_assoc := λ x y => sorry,
  -- add_zero := λ x => sorry,
  -- add_comm:= λ x y => sorry,
  -- add_left_neg:= λ x => sorry,
  -- left_distrib:= λ x y => sorry,
  -- right_distrib:= λ x y => sorry,
  -- one_mul:=λ x => sorry,
  -- mul_zero:= λ x => sorry,
  -- mul_assoc:= λ x y => sorry,
  -- mul_one:= λ x => sorry,
  -- mul_inv_cancel:= λ x y => sorry,
  -- mul_comm:= λ x y => sorry,
  -- zsmul:= λ x y => sorry,
  -- qsmul:= λ x y => sorry,
  -- exists_pair_ne:= sorry,
  -- nnqsmul:= λ x y => sorry,
  -- nsmul:= λ x y => sorry,

end HyperGenerals
end Hypers
