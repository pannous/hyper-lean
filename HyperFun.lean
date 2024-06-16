-- import data.real.basic -- Import basic real number theory in LEAN 3
import Mathlib.Data.Real.Basic -- Import basic real number theory in LEAN 4
import Mathlib.Data.Real.Ereal -- ∞
import Mathlib.Data.Real.Hyperreal -- defined as hyperfilter germ
import Init.Data.Nat.Basic
import Init.Prelude
import Init.Control.Basic -- Import basic control structures in LEAN 4

-- def Hyperreal : Type := Germ (hyperfilter ℕ : Filter ℕ) ℝ deriving Inhabited
notation "∞" => (⊤ : EReal)
notation "-∞" => (⊥ : EReal)

-- scoped notation "ε" => epsilon
-- scoped notation "ω" => omega

namespace Hypers
section HyperFun

-- Avoid Real Numbers When Possible:
-- If the use of real numbers introduces complexity due to issues like non-decidability of equality, consider if your application can tolerate using rational numbers or fixed-point arithmetic, which do not have these issues in Lean.

def Comps := List (ℝ × ℝ)
-- def Comps := List (ℝ × ℚ) -- what about ε^π :) seriously, needed in e^πi = -1
-- def Comps := List (ℝ × ℤ) -- ℤ for exponents integer powers of ε and ω enough for now
-- def Comps := List (ℚ × ℚ)  -- but what about π?


-- structure HyperFun :=
--   components : List (ℝ × ℤ) -- [(3, 0), (1, 1), (2, -2)] => 3 + ω + 2ε^2 -- note ε = ω⁻¹

structure HyperFun :=
  components : ℤ → ℝ  -- generalized for infinite lists of
  order : ℕ -- limit the range of non-zero components e.g. ε^2 + ω^3 => order = 3


-- notation "ℚ*" => HyperFun -- but what about π?
notation "ℝ⋆" => HyperFun -- may conflict with Hyper from Hyper.lean
-- notation "ℝ*" => HyperFun -- may conflict with Lean 4 notation for hyperreals

instance : Zero HyperFun where
  zero := { components := fun _ => 0, order := 0}

instance : One HyperFun where
  one := { components := fun x => if x = 0 then 1 else 0, order := 0}

instance : Inhabited HyperFun where
  default := Zero.zero

def epsilon : HyperFun := { components := fun x => if x = -1 then 1 else 0, order := 1}
-- def omega : HyperFun := { components := fun x => if x = 1 then 1 else 0 }
def omega : HyperFun := { components := fun x => match x with | 1 => 1 | _ => 0, order := 1}
-- see which one works better: if or match

scoped notation "ε" => epsilon
scoped notation "ω" => omega

-- coercion from reals to hyperreals
instance : Coe ℝ ℝ⋆ where
  coe r := { components := fun x => if x = 0 then r else 0, order := 0}

instance : Coe ℕ ℝ⋆ where
  coe (n:ℕ) : HyperFun := { components := fun x => if x = 0 then n else 0, order := 0}


-- instance : FunLike HyperFun ℤ ℝ where
--   coe f := f.components
--   coe_injective' := λ f g hfg => by sorry


instance : HAdd ℚ (ℤ → ℝ) (ℤ → ℝ) where -- needed? works without it!
  hAdd q f := fun x => q + f x

instance : HAdd (ℤ → ℝ) (ℤ → ℝ) (ℤ → ℝ) where -- needed??
  hAdd q f := fun x => q x + f x

-- q • f = q * f
instance : HMul ℚ (ℤ → ℝ) (ℤ → ℝ) where -- needed!
  hMul q f := fun x => q * f x

instance : HSMul ℚ (ℤ → ℝ) (ℤ → ℝ) where -- same as HMul?
  hSMul q f := fun x => q * f x

instance : HSMul ℕ (ℤ → ℝ) (ℤ → ℝ) where -- same as HMul?
  hSMul q f := fun x => q * f x

-- lemma hsmul_def (q : ℚ) (f : ℤ → ℝ) : q • f = fun x => q * f x := rfl
lemma one_mul (f : ℤ → ℝ) : 1 * f = f := by
  apply funext -- (∀ x, f x = g x) → f = g
  intro x
  {show 1 * f x = f x; simp; }


-- lemma one_mul2 (f : ℤ → ℝ) : 1 * f = f := by
--   ext
--   {show ∀ x : 1 * f x = f x; simp; }

instance : HSMul ℚ HyperFun HyperFun where
  -- hSMul q f := { components := fun x => q * f.components x, order := f.order }
  hSMul q f := { components := q * f.components, order := f.order }

instance : HSMul ℕ HyperFun HyperFun where
  hSMul n f := { components := n * f.components, order := f.order }
  -- hSMul q f := { components := fun x => q * f.components x, order := f.order }


instance : HMul ℚ HyperFun HyperFun where
  hMul q f := { components := q * f.components, order := f.order }

instance : HMul ℕ HyperFun HyperFun where
  hMul n f := { components := n * f.components, order := f.order }


instance : Add HyperFun where
  add f g := {
    -- components := f.components + g.components , -- uses macro_rules `(binop% HAdd.hAdd $x $y)
    components := fun x => f.components x + g.components x,
    order := max f.order g.order
    }

-- instance : HAdd HyperFun HyperFun HyperFun where
--   hAdd := Add.add


-- instance : Mul HyperFun where
--   mul f g := { components := fun x => ∑ (i : ℤ) , f.components x * g.components (x - i) }

instance : Mul HyperFun where
  mul f g := {
    components := fun x =>
      let indices := List.range (2 * max f.order g.order + 1) |>.map (fun n => n - max f.order g.order)
      List.foldl (fun acc i => acc + f.components (x + i) * g.components (x - i)) 0 indices
      -- indices.sum fun i => f.components (x + i) * g.components (x - i)
      ,
    order := f.order + g.order,
  }


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


lemma one_mul2 (a : HyperFun) : ((1:ℕ) • a) = a := by
  apply HyperFun.ext -- (∀ x, f x = g x) → f = g
  {
  -- show ((1:ℕ) • a).components = a.components
  calc
    ((1:ℕ) • a).components = 1 * a.components := by simp [HSMul.hSMul]
    _ =  a.components := by rw [one_mul]
  }
  {show a.order = a.order; simp; }

lemma one_mul3 (a : HyperFun) : (1:ℕ) * a = a := by
  ext x
  {show 1 * a.components = a.components; simp; }
  {show a.order = a.order; simp; }



lemma one_mulx (f : HyperFun) : 1 * f = f := by
  -- ext
  apply HyperFun.ext
  intro x
  {show 1 * f.components x = f.components x; rw [one_mul]; }
  {show 1 * f.order = f.order; rw [Nat.mul_one]; }

lemma add_zero (f : HyperFun) : f + 0 = f := by
  ext
  {show f.components + 0.components = f.components; rw [List.add_zero]; }
  {show max f.order 0.order = f.order; rw [Nat.max_eq_left]; }

-- #eval (1:ℝ⋆) + 1
#eval One.one + One.one

lemma add_assoc (f g h : HyperFun) : (f + g) + h = f + (g + h) := by
    ext
    -- simp [Add.add]
    -- intro x -- ∀ (x : ℤ),  needed when using apply HyperFun.ext, but NOT with ext keyword!?
    {show
      (f.components + g.components) + h.components =
       f.components + (g.components + h.components); rw [add_assoc]; rfl}
    {show max (max f.order g.order) h.order = max f.order (max g.order h.order); rw [Nat.max_assoc]; }
    -- {show (f.order + g.order) + h.order = f.order + (g.order + h.order); rw Nat.add_assoc; rfl}


end HyperFun
end Hypers
