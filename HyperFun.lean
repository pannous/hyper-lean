import Mathlib.Data.Real.Basic -- Import basic real number theory in LEAN 4
import Mathlib.Data.Real.Ereal -- ∞
import Mathlib.Data.Real.Hyperreal -- defined as hyperfilter germ
import Init.Data.Nat.Basic
import Init.Prelude
import Init.Control.Basic -- Import basic control structures in LEAN 4
import Hyper.HyperUtil
import Lean
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

instance : Zero HyperFun where
  zero := { components := fun _ => 0, order := 0}
def zero := (0:HyperFun)

instance : One HyperFun where
  one := { components := fun x => if x = 0 then 1 else 0, order := 0}
  -- one := { components := 1, order := 0 } -- danger, don't evaluate outside order! fails for one + epsilon
--  one := { components := λ match with . 0 => 1 }
--                     | 0 => 1
--                     | _ => 0,⦄
--   one := { components := fun x => match x with | 0 => 1 | _ => 0, order := 0}
-- def one := (1:HyperFun) -- One.one -- stuck!?
notation "one" => (1:HyperFun)

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

def maxNonZeroExponent (f : HyperFun) : ℤ :=
  let size : Nat := 2 * f.order + 1
  let offsets := List.range size
  let found := offsets.map (λ x => if f.components (x - f.order) ≠ 0 then x - f.order else -f.order)
  found.maximum.get!

instance LT : LT HyperFun where
  lt f g := maxNonZeroExponent f < maxNonZeroExponent g
  ∨ maxNonZeroExponent f = maxNonZeroExponent g ∧ f.components (maxNonZeroExponent f) < g.components (maxNonZeroExponent g)

--  reuse Util pair ordering:
-- instance : LT (T × T) where
--   lt := λ a b => a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)

def hyperFunToTuple (f : HyperFun) : ℤ × ℚ :=
  (maxNonZeroExponent f, f.components (maxNonZeroExponent f))

-- instance LE : LE HyperFun where
--   le f g := ∀ x, f.components x ≤ g.components x

-- instance LT : LT HyperFun where
--   lt f g := ∀ x, f.components x < g.components x


 #eval zero < one
--  #eval one < zero

-- coercion from reals etc to hyperreals
instance : Coe ℝ 𝔽* where
  coe r := { components := fun x => if x = 0 then (r:𝔽) else 0, order := 0}

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
      if x > order + order then 0
      else ∑ i < 2*order + 1, f.components (i - order) * g.components (x - i + order)
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

--
-- instance : Add HyperFun where
--   add f g := {
--     components := f.components + g.components , -- uses macro_rules `(binop% HAdd.hAdd $x $y)
--     -- components := fun x => f.components x + g.components x,
--     order := max f.order g.order
--     }

lemma hyper_one_plusX  : one + one = (2:𝔽*) := by
  ext x
  show (one + one).components x= (2: HyperFun).components x
  calc
  -- one := { components := fun x => match x with | 0 => 1 | _ => 0, order := 0}
    (one + one).components x = HyperFun.components 1 x + HyperFun.components 1 x := by rfl
    _ = match x with
      | 0 => 1 + 1
      | _ => 0 + 0 := by
      match x with
      | 0 => rfl
      | _ => sorry
    -- (1 + 1).components x= (one + one).components x:= by rfl
    _ = (2:HyperFun).components x := by rfl --sorry
    -- _ = match x with
    --   | 0 => (1:𝔽).components 0 + f.components 0
    --   | _ => 0 + f.components x := by
    --   match x with
    --   | 0 => rfl
    --   | _ => rw [zero_add]
  {show (one + one).order = (2:𝔽*).order; simp; }


lemma hyper_one_plus  : one + one = (2:𝔽*) := by
  apply HyperFun.ext
  show (one + one).components= (2: HyperFun).components
  calc
    (1 + 1).components = (one + one).components:= by rfl
    _ = (2:𝔽*).components := by sorry
    -- _ = match x with
    --   | 0 => (1:𝔽).components 0 + f.components 0
    --   | _ => 0 + f.components x := by
    --   match x with
    --   | 0 => rfl
    --   | _ => rw [zero_add]
  {show a.order = a.order; simp; }


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

end HyperFun
end Hypers
