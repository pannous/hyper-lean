-- import Mathlib.Data.Int.AbsoluteValue
-- import Mathlib
import Mathlib.Data.Real.Basic -- Import basic real number theory in LEAN 4
import Mathlib.Data.Real.Ereal -- ∞
import Mathlib.Data.Real.Hyperreal -- defined as hyperfilter germ
import Init.Data.Nat.Basic
import Init.Prelude
import Init.Control.Basic -- Import basic control structures in LEAN 4
import Hyper.HyperUtil
import Lean
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

--- ⚠️ 💡  implement hyperreal numbers via a function of their coefficients π*ε =>  f(-1)=π
--- This very general approach seems to be overkill and hard for proofs see hypergeneral for a list based implementation

#eval Float.sin 0
-- #eval Real.sin 0  -- abstract function!
-- import data.real.basic -- Import basic real number theory in LEAN 3


namespace Hypers
section HyperFun

-- Avoid Real Numbers When Possible:
-- If the use of real numbers introduces complexity due to issues like non-decidability of equality, consider if your application can tolerate using rational numbers or fixed-point arithmetic, which do not have these issues in Lean.

notation "𝔽" => ℚ -- our field, true alias
-- def 𝔽 := ℚ -- treats it as own Type! needs own instance : …

-- A grading is a decomposition of an algebraic structure into components indexed by a set (often the non-negative integers). The operations must preserve this decomposition.
structure HyperFun :=
  components : ℤ → 𝔽  -- terms for exponents e.g. (3ω⁻¹ + 1 + 3ω²) finite list:
  order : ℕ -- limit the range of non-zero components e.g. ε^2 + ω^3 => order = 3

notation "𝔽*" => HyperFun
notation "F*" => HyperFun

-- notation "xxx" => Int

instance : Zero HyperFun where
  zero := { components := fun _ => 0, order := 0}
def zero := (0:HyperFun)

instance : One HyperFun where -- One.one
  one := { components := fun x => if |x| > 0 then 0 else 1, order := 0}
  -- one := { components := fun x => if x = 0 then 1 else 0, order := 0}
  -- one := { components := 1, order := 0 } -- danger, don't evaluate outside order! fails for one + epsilon
--  one := { components := λ match with . 0 => 1 }
--                     | 0 => 1
--                     | _ => 0,⦄
--   one := { components := fun x => match x with | 0 => 1 | _ => 0, order := 0}
-- def one := (1:HyperFun) -- One.one -- stuck!?
notation "one" => (1:HyperFun)

-- alternative equivalent definition of one
def one' : HyperFun :=
  { components := fun x => if x = 0 then 1 else 0, order := 0 }


instance : Inhabited HyperFun where
  default := Zero.zero


def epsilon : HyperFun := { components := fun x => if x = -1 then 1 else 0, order := 1}
-- def omega : HyperFun := { components := fun x => if x = 1 then 1 else 0 }
def omega : HyperFun := { components := fun x => match x with | 1 => 1 | _ => 0, order := 1}
-- see which one works better: if or match

scoped notation "ε" => epsilon
scoped notation "ω" => omega


-- instance : ToNat HyperFun Zero.zero where
--   toNat := 0

instance : OfNat HyperFun 0 where
  ofNat := Zero.zero

instance : OfNat HyperFun 1 where
  ofNat := One.one

instance : OfNat HyperFun n where
  ofNat := ⟨ fun x => if x = 0 then n else 0, 0 ⟩
--   ofNat := ⟨ fun x => n * (x == 0), 0 ⟩
  -- ofNat := { components := fun x => if x = 0 then n else 0, order := 0}

#eval List.range 10  -- generates [0, 1, 2, ..., 9]
#eval (List.range 10).maximum.get!
-- Function to find the highest exponent with a non-zero coefficient within the range [-order, order]


-- coercion from reals etc to hyperreals
-- instance : Coe ℝ 𝔽* where
  -- coe r := { components := fun x => if x = 0 then (r:𝔽) else 0, order := 0}

instance : Coe ℚ 𝔽* where
  coe q := { components := fun x => if x = 0 then q else 0, order := 0}

instance : Coe ℕ 𝔽* where
  coe (n:ℕ) : HyperFun := { components := fun x => if x = 0 then n else 0, order := 0}

-- instance : FunLike HyperFun ℤ 𝔽 where
--   coe f := f.components
--   coe_injective' := λ f g hfg => by sorry


instance : HAdd 𝔽 (ℤ → 𝔽) (ℤ → 𝔽) where -- needed? works without it!
  hAdd q f := fun x => q + f x

instance : HAdd (ℤ → 𝔽) (ℤ → 𝔽) (ℤ → 𝔽) where -- needed??
  hAdd q f := fun x => q x + f x

-- q • f ≈ q * f
instance : HMul ℚ (ℤ → 𝔽) (ℤ → 𝔽) where -- needed!
  hMul q f := fun x => q * f x

instance : HMul 𝔽 (ℤ → 𝔽) (ℤ → 𝔽) where -- needed!
  hMul q f := fun x => q * f x

-- homogeneous scalar multiplication
instance : HSMul 𝔽 (ℤ → 𝔽) (ℤ → 𝔽) where -- same as HMul / SMul ?
  hSMul q f := fun x => q * f x

instance : HSMul ℕ (ℤ → 𝔽) (ℤ → 𝔽) where
  hSMul q f := fun x => q * f x

instance : HSMul ℕ (ℤ → 𝔽) (ℤ → 𝔽) where
  hSMul q f := fun x => q * f x

-- lemma hsmul_def (q : 𝔽) (f : ℤ → 𝔽) : q • f = fun x => q * f x := rfl

lemma one_mul (f : ℤ → 𝔽) : 1 * f = f := by
  -- sorry
  simp
  -- apply funext -- (∀ x, f x = g x) → f = g
  -- intro x
  -- show 1 * f x = f x; simp;

-- homogeneous scalar multiplication
-- homogeneous here means that the order of the function is preserved
instance : HSMul 𝔽 HyperFun HyperFun where
  hSMul q f := { components := q * f.components, order := f.order } -- pointfree
  -- hSMul q f := { components := fun x => q * f.components x, order := f.order } -- explicit

instance : HSMul ℕ HyperFun HyperFun where
  hSMul n f := { components := n * f.components, order := f.order }  -- pointfree
  -- hSMul q f := { components := fun x => q * f.components x, order := f.order }  -- explicit


instance : HMul 𝔽 HyperFun HyperFun where
  hMul q f := { components := q * f.components, order := f.order } -- pointfree
  -- hMul q f := { components := fun x => q * f.components x, order := f.order } -- explicit


instance : HMul ℕ HyperFun HyperFun where
  hMul n f := { components := n * f.components, order := f.order }

-- Add.add
instance : Add HyperFun where
  add f g := {
    components := f.components + g.components , -- uses macro_rules `(binop% HAdd.hAdd $x $y)
    -- components := fun x => f.components x + g.components x,
    order := max f.order g.order
    }

instance : HAdd HyperFun HyperFun HyperFun where -- not homogenous since order is not preserved?
  hAdd := Add.add

-- instance : Mul HyperFun where
--   mul f g := { components := fun x => ∑ (i : ℤ) , f.components x * g.components (x - i) }


-- Mul.mul
instance : Mul HyperFun where
  mul f g := {
    order := f.order + g.order,
    components := fun x =>
    -- say max orders are 2 and 2
      -- fun(4) = f(2)*g(2)    -- ω² * ω²
      -- fun(3) = f(2)*g(1) + f(1)*g(2)
      -- fun(2) = f(2)*g(0) + f(1)*g(1) + f(0)*g(2)
      -- fun(1) = f(2)*g(-1) + f(1)*g(0) + f(0)*g(1) + f(-1)*g(2)
      -- fun(0) = f(2)*g(-2) + f(1)*g(-1) + f(0)*g(0) + f(-1)*g(1) + f(-2)*g(2)  -- ω*ε=1
      -- fun(-1) = f(1)*g(-2) + f(0)*g(-1) + f(-1)*g(0) + f(-2)*g(1)
      -- fun(-2) = f(0)*g(-2) + f(-1)*g(-1) + f(-2)*g(0)
      -- fun(-3) = f(-1)*g(-2) + f(-2)*g(-1)
      -- fun(-4) = f(-2)*g(-2)
      let order := f.order + g.order
      if |x| > order + order then 0
      else ∑ i in Finset.range (2 * order + 1), f.components (i - order) * g.components (x - i + order)
      -- else ∑ i < 2*order + 1, f.components (i - order) * g.components (x - i + order)
  }

instance : Neg HyperFun where
  neg f := { components := fun x => - f.components x, order := f.order }

instance : Sub HyperFun where
  sub f g := f + -g

instance : Inv HyperFun where
  inv f := { components := fun x => 1 / f.components (-x), order := f.order }

-- for Lean.MetaEval for #eval
instance : Repr HyperFun where
  reprPrec f := λ n =>
    Id.run do
      let mut output := ""
      for j in [0: 2*f.order + 1] do
        let i : ℤ := j - f.order
        let c := f.components i
        if c ≠ 0 then
          -- if i = 0 then
          --   if output = "" then
          --     output := toString c
          --   else
          --     output := output ++ " + " ++ toString c
          -- else
          --   if output = "" then
          --     output := toString c ++ "ω^" ++ toString i -- ε
          --   else
              output := output ++ " " ++ toString c ++ "ω^" ++ toString i -- ε
      if output = "" then
        output := "0"
      pure output


def Hyper.hPow (a : HyperFun) (b : ℕ) : HyperFun :=
  match b with
  | 0 => 1
  | n + 1 => a * hPow a (n)
  decreasing_by
    simp_wf

instance : HPow HyperFun ℕ HyperFun where
   hPow a b := Hyper.hPow a b

instance : HPow HyperFun ℤ HyperFun where
  hPow a b :=
    if b > 0 then
      Hyper.hPow a b.natAbs
    else if b = 0 then
      1
    else
      Hyper.hPow a⁻¹ b.natAbs

instance : Div HyperFun where
  div x y := x * y⁻¹ -- via inverse


@[ext] -- apply HyperFun.ext_all equivalent to "ext x"
theorem HyperFun.ext_all {f g : HyperFun}
(component_goal : ∀ x, f.components x = g.components x) (order_goal : f.order = g.order) : f = g := by
  cases f;
  cases g;
  congr;
  exact funext component_goal
  -- order_goal implicit !?!

@[ext]
theorem HyperFun.ext {f g : HyperFun} -- POINT FREE version of HyperFun.ext_all
  (component_goal : f.components = g.components) (order_goal : f.order = g.order) : f = g := by
  cases f;
  cases g;
  congr;


-- @[ext]
-- theorem HyperFun.ext2 (h : ∀ {f g : HyperFun}, f.components = g.components ∧ f.order = g.order → f = g)
--   {f g : HyperFun} : f = g := by
--   cases f
--   cases g
--   congr
  -- split
  -- cases g
  -- congr;
  -- exact funext h



-- -- @[ext]
-- theorem HyperFun.ext3 :
--   ∀ {f g : HyperFun},
--   (f.components = g.components) ∧ (f.order = g.order) → f = g := by
--   intros f g h
--   cases f
--   cases g
--   -- let h := (f.components = g.components)
-- --   -- intros f g h,
--   -- simp only [and_imp, Prod.mk.inj_iff]
--   congr
--   rw [funext]

-- lemma zero_is_zero : (0 : HyperFun) = 0 := rfl
lemma zero_is_zero : HyperFun.components 0 = 0 := by rfl

-- Lemma to prove zero addition property
lemma zero_add_fun (a : HyperFun) : (0 : HyperFun) + a = a := by
  apply HyperFun.ext
  { calc -- Proving component-wise equality
    (0 : HyperFun).components + a.components = 0 + a.components := rfl
    _ = a.components := by funext; simp [zero_add]
  }
  { -- Proving order equality
  show max (0 : HyperFun).order a.order = a.order
  apply max_eq_right; exact zero_le a.order
  }


-- Lemma to prove zero addition property
lemma zero_add_fun_v2 (a : HyperFun) : (0 : HyperFun) + a = a := by
  apply HyperFun.ext
  show (0 : HyperFun).components + a.components = a.components
  simp [zero_add]
  rfl
  apply max_eq_right; exact zero_le a.order


-- Lemma to prove zero addition property
-- lemma zero_add_fun_v3 (a : HyperFun) : (0 : HyperFun) + a = a := by
--   ext -- but apply HyperFun.ext OK!?
--   show (0 : HyperFun).components + a.components = a.components
--   simp [zero_add]
--   rfl
--   apply max_eq_right; exact zero_le a.order


-- Proving 0 + a = a for any HyperFun 'a'
lemma zero_add_fun_via_all_x (a : HyperFun) : (0 : HyperFun) + a = a := by
  ext x -- apply HyperFun.ext_all ∀ x
  { -- Proving component-wise equality
  -- intro x
  -- show (0 : HyperFun).components x + a.components x = a.components x
  calc -- ONLY WORKING Example of calc so far!!
    (0 : HyperFun).components x + a.components x = 0 + a.components x := by rfl
    _ = a.components x := by rw [zero_add]
  }
  { -- Proving order equality
  show max (0 : HyperFun).order a.order = a.order
  calc
    max (0 : HyperFun).order a.order = max 0 a.order := by rfl
    _ = a.order := by apply max_eq_right; exact zero_le a.order
  }


lemma one_hsmul (a : HyperFun) : ((1:ℕ) • a) = a := by
  apply HyperFun.ext
  {calc -- show ((1:ℕ) • a).components = a.components
    ((1:ℕ) • a).components = 1 * a.components := by simp [HSMul.hSMul]
    _ =  a.components := by rw [one_mul] }
  {show a.order = a.order; simp; }

-- instance : One HyperFun where
--   one := { components := fun x => if x = 0 then 1 else 0, order := 0}

-- instance : Add HyperFun where
--   add f g := {
--     components := f.components + g.components , -- uses macro_rules `(binop% HAdd.hAdd $x $y)
--     -- components := fun x => f.components x + g.components x,
--     order := max f.order g.order
--     }


-- too many stupid sub-lemma,  how to inline?
lemma one_of_one: (HyperFun.components one) 0 = 1 := by
  rfl

lemma one_of_one0 (x : ℤ) (h : x = 0) : (HyperFun.components one) x = 1 := by
   simp [h,one_of_one]

-- Lemma to prove that HyperFun.components one x = 0 for any x ≠ 0
lemma one_of_any (x : ℤ) (h : x ≠ 0) : (HyperFun.components one) x = 0 := by
  calc
    -- (HyperFun.components one) x = if x = 0 then 1 else 0 := by rfl
    (HyperFun.components one) x = if |x| > 0 then 0 else 1 := by rfl
    _ = 0 := by simp [h]


-- Lemma to prove that one + one equals a function returning 2 when x = 0
lemma hyper_one_plusX : one + one = (2:𝔽*) := by
  ext x
  show (one + one).components x = (if x = 0 then 2 else 0)
  calc
    (one + one).components x = (HyperFun.components one) x + (HyperFun.components one) x := by rfl
      _ = if h: x = 0 then 2 else 0 := by
        split_ifs with h
        { -- case x = 0
        calc
          HyperFun.components 1 x + HyperFun.components 1 x = 1 + 1 := by rw [one_of_one0 x h]
          _ = 2 := by rfl
        }
        { -- case x ≠ 0
        calc
          HyperFun.components 1 x + HyperFun.components 1 x = 0 + 0 := by rw [one_of_any x h]
          _ = 0 := by simp
        }
  {show (one + one).order = (2:𝔽*).order; rfl}


lemma one_equiv_one' : one = one' := by
  sorry
/--/
  ext x
  -- Show components are equivalent
  show (1 : HyperFun).components x = one'.components x
  calc
    (1 : HyperFun).components x
        = if |x| > 0 then 0 else 1 := by rfl
    _ = if x = 0 then 1 else 0 := by
      split_ifs
      -- case
      {
        have : |x| = 0 := by linarith
        rw [this]
        rfl
      }
      {
        have : |x| > 0 := by linarith
        simp [this]
      }
  -- Show orders are equivalent
  show (1 : HyperFun).order = one'.order
  rfl
-/

lemma one_of_0_is_1: (HyperFun.components one) 0 = 1 := by
  rfl

lemma one_of_x0_is_1 (x : ℤ) (h : x = 0) : (HyperFun.components one) x = 1 := by
  rw [one_equiv_one']
  calc
    one'.components x = if x = 0 then 1 else 0 := by rfl
    _ = 1 := by simp [h]

    -- (HyperFun.components one) x = if |x| > 0 then 0 else 1 := by rfl

lemma one_of_x_is_zero (x : ℤ) (h : x ≠ 0) : (HyperFun.components one) x = 0 := by
  rw [one_equiv_one']
  calc
    (HyperFun.components one') x = if x = 0 then 1 else 0 := by rfl
    _ = 0 := by simp [h]


lemma x_zero_means_abs_zero (x : ℤ) : x=0  → ¬ |x| > 0  := by
  intro h
  rw [h]
  simp

lemma abs_of_neg_pos (x : ℤ) : x < 0 → |x| > 0 := by
  intro h
  simp [abs]
  #find neg_pos_of_neg
  -- exact Int.neg_pos_of_neg h
  sorry

lemma abs_of_neg (x : ℤ) : x < 0 → |x| = -x := by
  intro h
  simp [abs]
  -- exact Int.neg_of_nat_of_lt h
  sorry


lemma x_not_zero_means_abs_not_zero (x : ℤ) : x ≠ 0 → |x| > 0 := by
  intro h
  cases x
  case ofNat n =>
    cases n
    · contradiction  -- This case is impossible because x ≠ 0
    · simp [abs]
      -- exact Nat.zero_lt_succ n
  case negSucc n =>
    simp [abs]
    -- #search negative_smaller_zero
    exact negative_smaller_zero h


lemma x_not_zero_means_abs_not_zeroB (x : ℤ) : x ≠ 0 → |x| > 0 := by
  intro h
  cases Int.lt_or_gt_of_ne h with -- a ≠ b →  a < b ∨ b < a
  | inl hlt =>
    exact abs_of_neg_pos x hlt
  | inr hgt =>
    have h: x > 0 → |x| > 0 := by sorry
    exact h hgt



-- lemma abs_x_gt_zero_means_x_not_zero  (x : ℝ) (h : abs x > 0) : x ≠ 0 := by
lemma abs_x_gt_zero_means_x_not_zero  (x : ℝ) (h : |x| > 0) : x ≠ 0 := by
  by_contra h0 -- … → x = 0 ⊢ False
  -- Insert the contradiction hypothesis
  subst h0 -- replace all variables of x with 0
  -- Simplify to find contradiction with the hypothesis `abs 0 > 0`
  simp only [abs_zero] at h
  -- Derive contradiction since `0 > 0` is false
  linarith


lemma not_abs_x_gt_zero_means_x_zero (x : ℤ) : ¬(|x| > 0) → x=0  := by
    intro h
    absurd h
    have : |x| > 0 := by
      cases x
      { -- case x = 0
        simp
        -- exact lt_irrefl 0 h
        sorry
      }
      { -- case x ≠ 0
        simp
      }
    contradiction

lemma not_abs_x_gt_zero_means_x_zero2 (x : ℤ) : ¬(|x| > 0) ↔ x=0  := by
  split
  { -- → direction
    intro h
    by_contra hx
    have : |x| > 0 := by
      cases abs_pos_iff.mpr hx
      assumption
    contradiction
  }
  { -- ← direction
    rintro rfl
    intro h
    have : |0| = 0 := by simp
    rw [this] at h
    exact lt_irrefl 0 h
  }

  -- use one := { components := fun x => match x with | 0 => 1 | _ => 0, order := 0}
  -- mul f g := {
  --     let order := f.order + g.order
  --     if x > order + order then 0
  --     else ∑ i < 2*order + 1, f.components (i - order) * g.components (x - i + order)
lemma hyper_one_mul_one (f : HyperFun) : one * one = one := by
  ext x
  {
    show (Mul.mul one one).components x = HyperFun.components 1 x
    let order := (one * 1).order
    have no_order : order = 0 := by rfl
    -- show (one * 1).components x = if x > 0 then 0 else HyperFun.components 1 x
    calc
      (one * 1).components x =
      if |x| > 0 then 0
        else ∑ i < 2*order + 1, (HyperFun.components 1 (i - order)) * (HyperFun.components 1 (x - i + order)) := by rfl
      _ = if |x| > 0 then 0   else ∑ i < 2*order + 1, ((1:F*).components (i - order)) * ((1:F*).components  (x - i + order)) := by rfl
      _ = if |x| > 0 then 0   else ∑ i < 2*order + 1, ((1:F*).components (i - 0)) * ((1:F*).components  (x - i + 0)) := by rfl
      _ = if |x| > 0 then 0   else ∑ i in Finset.range (2 * 0 + 1), HyperFun.components 1 (↑i - 0) * HyperFun.components 1 (x - ↑i + 0) := by rfl
      _ = if |x| > 0 then 0   else ∑ i in Finset.range 1, HyperFun.components 1 (↑i) * HyperFun.components 1 (x - ↑i) := by simp
      -- _ = if x > 0 then 0   else ∑ i < (2 * 0 + 1), HyperFun.components 1 (↑i - 0) * HyperFun.components 1 (x - ↑i + 0) := by rw [no_order]
      _ = if |x| > 0 then 0   else ((1:F*).components 0) * (1:F*).components x := by simp
      -- _ = if |x| > 0 then 0 else (1 : 𝔽*).components 0 * (1 : 𝔽*).components x := by simp [Finset.range, Finset.sum_singleton]
      _ = if h:|x| > 0 then 0 else (1 : 𝔽*).components 0 * (1 : 𝔽*).components 0 := by
        split_ifs
        -- -- case pos
        { simp }
        -- -- case nonpos
        {
          have : x = 0 := by
            rw [←not_abs_x_gt_zero_means_x_zero x h✝]
            -- exact not_lt_of_ge (le_of_eq rfl)
          rw [this]
          -- have : x = 0 := by rw [not_abs_x_gt_zero_means_x_zero]
        --   -- have : x = 0 := by linarith
        --   rw [this]
        --   -- simp
        }
      _ = if |x| > 0 then 0 else HyperFun.components 1 0 * HyperFun.components 1 0 := by rfl
      _ = if |x| > 0 then 0 else 1 * 1 := by rw [one_of_0_is_1]
      _ = if |x| > 0 then 0 else 1 := by simp
      _ = HyperFun.components 1 x := by rw [One.one]
   }
  {show (one * one).order = (1:𝔽*).order; rfl}




lemma hyper_one_mulx (f : HyperFun) : 1 * f = f := by
  ext x
  {
    show (1 * f).components x= f.components x
    calc
    (1 * f).components x = (one * f).components x:= by rfl
    -- use one := { components := fun x => match x with | 0 => 1 | _ => 0, order := 1}
  -- mul f g := {
  --     let order := f.order + g.order
  --     if x > order + order then 0
  --     else ∑ i < 2*order + 1, f.components (i - order) * g.components (x - i + order)
    _ = match x with
      | 0 => (1:𝔽) * f.components 0
      | _ => 0 * f.components x := by
      match x with
      | 0 => rfl
      | _ => rfl
    _ = f.components x                   := by
                                              funext x;
                                              match x with
                                              | 0 => rfl
                                              | _ => rfl

    _ = f.components := by rw [one_mul];

  }
  -- ext x
  -- {show 1 * f.components x = f.components x; rw [one_mul]; }
  -- {show 1 * f.order = f.order; rw [Nat.mul_one]; }

lemma add_zero (f : HyperFun) : f + 0 = f := by
  ext
  {show f.components + 0.components = f.components; rw [List.add_zero]; }
  {show max f.order 0.order = f.order; rw [Nat.max_eq_left]; }


lemma add_assoc (f g h : HyperFun) : (f + g) + h = f + (g + h) := by
    ext
    -- simp [Add.add]
    -- intro x -- ∀ (x : ℤ),  needed when using apply HyperFun.ext, but NOT with ext keyword!?
    {show
      (f.components + g.components) + h.components =
       f.components + (g.components + h.components); rw [add_assoc]; rfl}
    {show max (max f.order g.order) h.order = max f.order (max g.order h.order); rw [Nat.max_assoc]; }
    -- {show (f.order + g.order) + h.order = f.order + (g.order + h.order); rw Nat.add_assoc; rfl}



-- Test cases
#eval 3²    -- 9
#eval 4.0⁻²   -- 0 assuming 1/16 is rounded down to 0

#eval (0:HyperFun)
#eval (1:HyperFun)
#eval ε
#eval ε⁻¹
#eval ε⁻²
#eval ε²
#eval ω
#eval ω²
#eval ω²+ε²
#eval ε*ω
#eval ω*ε
#eval ω*ω
#eval ω⁻¹
#eval ω^2
#eval ω^(-3)
#eval 2/ω
#eval one
#eval one + zero
#eval one + one
#eval one + epsilon

#eval (1:𝔽*) + 1
-- #eval One.one + One.one



-- instance : BEq (ℤ → Rat) where
--   beq f g := List.all (fun x => f x == g x) (List.range 201).map (fun x => x - 100)

def boundedEq (f g : HyperFun) : Prop :=
  ∀ x : ℤ, |x| ≤ f.order → f.components x = g.components x


-- Provide an instance of Decidable for boundedEq
instance boundedEqDecidable (f g : HyperFun) : Decidable (boundedEq f g) :=
  sorry

instance : BEq HyperFun where
  beq f g := f.order = g.order && decide (boundedEq f g)
  --decide (∀ x : ℤ, |x| ≤ f.order → f.components x == g.components x)


def maxNonZeroExponent (f : HyperFun) : ℤ :=
  -- if f==zero then -1000 else
  let size : Nat := 2 * f.order + 1
  let offsets := List.range size
  -- let found := offsets.map (λ x => if f.components (x - f.order) ≠ 0 then x - f.order else -f.order)
  let found := offsets.map (λ x => if f.components (x - f.order) ≠ 0 then x - f.order else -1000)
  found.maximum.get!

-- instance : LT HyperFun where
--   lt f g := maxNonZeroExponent f < maxNonZeroExponent g
--   ∨ maxNonZeroExponent f = maxNonZeroExponent g ∧ f.components (maxNonZeroExponent f) < g.components (maxNonZeroExponent g)

--  reuse Util pair ordering:
-- instance : LT (T × T) where
--   lt := λ a b => a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)


-- instance genericPairOrder: LT (T × S) where
--   lt := λ a b => a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)

-- instance genericPairsDecidableRel: DecidableRel (LT.lt : T × S → T × S → Prop) := …


def hyperFunToTuple (f : HyperFun) : ℤ × ℚ :=
    (maxNonZeroExponent f, f.components (maxNonZeroExponent f))

#eval hyperFunToTuple (1:HyperFun)
#eval hyperFunToTuple (0:HyperFun)
#eval hyperFunToTuple epsilon

instance : LT HyperFun where
  lt f g := hyperFunToTuple f < hyperFunToTuple g


-- Prove that the LT relation for HyperFun is equivalent to LT for ℤ × ℚ
theorem hyperFun_lt_iff_tuple_lt (f g : HyperFun) :
  f < g ↔ hyperFunToTuple f < hyperFunToTuple g := by sorry

instance : DecidableRel (LT.lt : HyperFun → HyperFun → Prop) :=
fun f g =>
  let fTuple := hyperFunToTuple f
  let gTuple := hyperFunToTuple g
  have hDec : Decidable (fTuple < gTuple) := genericPairsDecidableRel fTuple gTuple
  match hDec with
  | isTrue hTuple =>
    isTrue (show f < g from by {
      unfold LT.lt;
      exact hTuple;
    })
  | isFalse hTuple =>
    isFalse (show ¬(f < g) from by {
      intro hfg;
      unfold LT.lt at hfg;
      exact hTuple hfg;
    })

 #eval zero < one
 #eval zero < epsilon
 #eval zero < -epsilon
--  #eval one < zero

section HyperDerivatives

def hyperDerivative0 (f : 𝔽* → 𝔽* ) : 𝔽*  :=
  f ε - f 0 / ε

#eval hyperDerivative0 (fun x => x^2)


def hyperDerivative (f : 𝔽* → 𝔽* ) : 𝔽* → 𝔽*  :=
  fun x => f (x + ε) - f (x) / ε

def hyperDerivativeOfConst (f : HyperFun) : HyperFun :=
{ components := fun x => f.components (x + 1) - f.components x, order := f.order - 1 }

notation "∂" => hyperDerivative
-- #eval ∂ Real.sin 0

end HyperDerivatives
end HyperFun
end Hypers
