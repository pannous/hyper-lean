import Mathlib.Data.Real.Basic -- Import basic real number theory in LEAN 4
-- import Mathlib.Data.Real.Ereal -- ∞
import Mathlib.Data.Real.Hyperreal -- defined as hyperfilter germ
-- import Mathlib.Data.Float.Basic -- Float
import Init.Data.Nat.Basic
-- import Init.Data.Float.Basic
import Init.Prelude
import Init.Control.Basic -- Import basic control structures in LEAN 4
import Lean
import Mathlib.Data.Real.Basic
-- import Mathlib.Data.Float.Basic
import Mathlib.Algebra.Order.Floor
-- import data.real.basic -- Import basic real number theory in LEAN 3


notation "∞" => (⊤ : EReal)
notation "-∞" => (⊥ : EReal)
notation "ℚ∞" => EReal -- ℚ±∞   ℚinf
notation "𝔽" => Float -- calculable implementation versus theoretical one

-- def Hyperreal : Type :=  Germ (hyperfilter ℕ : Filter ℕ) ℚ deriving Inhabited

namespace Hypers
section HyperQ -- HyperRationals

-- Approximation of Hyper numbers with ℚ (rationals) (versus floats)

-- Define the structure of hyperreal numbers
-- after all proofs are done, we can set fields to Float 𝔽 or Rational ℚ for evaluation
structure Hyper :=
  real_part : ℚ
  epsilon_part : ℚ -- ε-part
  infinite_part : ℚ -- ω-part
  exceptional : Bool -- NaN or ε² or ±∞
  -- higher orders ω² not implemented here => ε² ≈ 0 and ω² ≈ ∞
  -- we can norm r + ε² to r and r + ε + ω + ω² to ∞
  -- deriving Repr not in lean 4


-- Outer and inner field extensions
structure HyperGeneral :=
  components : List (ℚ × ℤ) -- [(3, 0), (1, 1), (2, -2)] => 3 + ω + 2ε^2 -- note ε = ω⁻¹
  -- components : ℤ → ℚ  functions for easier handling!


def getComponent (components : List ℚ) (index : ℕ) : Option ℚ :=
  components.get? index
-- infix:50 "!["  => λ (l : List ℚ) (i : ℕ) => getComponent l i
-- postfix:50 "]"  => λ (i : ℕ) => i
-- #eval [1, 2, 3] ![ 1 ] -- 2


structure HyperSimple := -- Not applicable for derivatives where we need x+ε ≠ x for ∂f(x)=(f(x+ε)-f(x))/ε   !
  components : ℚ × ℤ  -- ONE of (3, 0), (1, 1), (2, -2) … => 3 or ω or 2ε^2 -- note ε = ω⁻¹
  -- components : ℚ × ℚ  -- ONE of (3, 0), (1, 1), (2, -2) … => 3 or ω or 2ε^2 -- note ε = ω⁻¹

-- @[inherit_doc]
notation "ℚ⋆" => Hyper  -- type \ R \ star <tab> for ℚ⋆
-- notation "ℚ*" => Hyper -- may conflict with Lean 4 notation for hyperreals

-- cast Nat to Prop / Bool
instance : OfNat Prop 0 where
  ofNat := false

instance : OfNat Prop 1 where
  ofNat := true

instance : OfNat Bool 0 where
  ofNat := false

instance : OfNat Bool 1 where
  ofNat := true

instance : Coe ℤ Bool where
  coe r := r ≠ 0

instance : Coe ℤ Prop where
  coe r := r ≠ 0


instance : One Hyper where
  one := ⟨1, 0, 0, 0⟩

-- Zero.zero
instance : Zero Hyper where
  zero := ⟨0, 0, 0, 0⟩


-- def zero := Zero.zero -- Hyper := ⟨0, 0, 0⟩ -- Hyper.0
-- def one : Hyper := ⟨1, 0, 0⟩
-- def ε : Hyper := ⟨0, 1, 0⟩
-- def ω : Hyper := ⟨0, 0, 1⟩
def epsilon : Hyper := ⟨0, 1, 0, 0⟩
def omega : Hyper := ⟨0, 0, 1, 0⟩

def Infinity :    Hyper := ⟨0, 0, 1, 1⟩ -- ω² ≈ ∞
def Infinisimal : Hyper := ⟨0, 0, 0, 1⟩ -- ε²
-- def Infinisimal : Hyper := ⟨0, 1, 0, 1⟩ -- ε²
def NotANumber :  Hyper := ⟨1, 0, 0, 1⟩ -- NaN
-- def Undefined :  Hyper := ⟨0, 0, 0, 1⟩ -- vs Infinisimal
def Minus_Infinity : Hyper := ⟨0, 0, -1, 1⟩ -- -ω² ≈ -∞
def Negative_Infinity : Hyper := ⟨0, 0, -1, 1⟩ -- -ω² ≈ -∞
-- def NotANumber : Hyper := ⟨*, 0, 0, 1⟩ -- NaN -- including 0,0,0,1 !

-- def Enfinisimal : Hyper := ⟨0, 1, 0, 1⟩ -- ε²
-- def Enfinity : Hyper := ⟨0, 0, 1, 1⟩ -- ω² ≈ ∞

-- scoped notation "0" => zero -- doesn't work "invalid atom"
-- notation "O" => zero
-- scoped notation "O" => Zero.zero
-- scoped notation "I" => One.one
scoped notation "ε" => epsilon
scoped notation "ω" => omega
scoped notation "ω²" => Infinity
scoped notation "∞" => Infinity
scoped notation "ε²" => Infinisimal
scoped notation "NaN" => NotANumber

-- todo: take float as rational (should be doable?)
-- object
-- instance : Coe 𝔽 ℚ where
--   coe r := (r:ℚ)

-- -- todo: take real as float (only lossfull!)
-- instance : Coe ℚ 𝔽 where
--   coe r := (r:𝔽)

-- instance : Coe 𝔽 ℚ⋆ where
--   coe r := Hyper.mk r 0 0 0

-- coercion from reals to hyperreals
-- instance : Coe ℝ ℚ⋆ where
--   coe r := Hyper.mk r 0 0 0

instance : Coe ℤ ℚ⋆ where coe r := Hyper.mk r 0 0 0
instance : Coe ℕ ℚ⋆ where coe r := Hyper.mk r 0 0 0
instance : Coe ℚ ℚ⋆ where coe r := Hyper.mk r 0 0 0


noncomputable
def realToInteger (r : ℝ) : ℤ := Int.ofNat (Nat.floor r)
-- def realToInteger (r : ℝ) : ℤ := Int.floor r
-- def realToInteger (r : ℝ) : ℤ := Int.ofNat (Float.floor (Float.ofReal r).toNat)

/-- Approximates a real number as a rational with specified precision -/
-- noncomputable
def toRationalApprox (r : ℝ) (precision : Nat := 1000000) : ℚ :=
  -- Use ToRat typeclass from Lean's standard library to convert a real to a rational
  -- This is a computable operation with bounded precision
  let n := (r * precision)
  ⟨n, precision⟩
  -- Rat.mk n precision

-- Use the computable version instead of the axiom
-- axiom closest_ratio : ℝ → ℚ -- arbitrary rational approximation (not computable)

instance : Coe ℝ ℚ⋆ where
  coe r := Hyper.mk (toRationalApprox r) 0 0 0

def hyper : ℝ → Hyper := λ r => ⟨(toRationalApprox r), 0, 0, 0⟩

-- Optionally, allow specifying precision for more accurate approximations
def hyperWithPrecision (r : ℝ) (precision : Nat := 1000000) : Hyper :=
  ⟨(toRationalApprox r precision), 0, 0, 0⟩

-- Adding a function to convert Hyper to ℝ with a standard part
def real (h : Hyper) : ℝ := h.real_part

instance : SMul ℚ ℚ⋆ where
  smul r x := ⟨r * x.real_part, r * x.epsilon_part, r * x.infinite_part , x.exceptional ⟩

instance : Neg Hyper where
  neg x :=
    ⟨-x.real_part, -x.epsilon_part, -x.infinite_part, x.exceptional⟩


instance : Add Hyper := ⟨
  λ x y => ⟨
    x.real_part + y.real_part,
    x.epsilon_part + y.epsilon_part,
    x.infinite_part + y.infinite_part,
    (x.exceptional || y.exceptional) -- for Bool
    ⟩
⟩

instance : Sub Hyper where
  sub x y := x + (-y)


instance : ToString ℚ where
  toString q :=
    if q.den = 1 then
      toString q.num  -- Just show the numerator if the denominator is 1
    else
      toString q.num ++ "/" ++ toString q.den

instance : ToString Bool where
  toString ja :=
    if ja then "true" else "false"

-- for Lean.MetaEval
instance : Repr Hyper where
  reprPrec h := λ n => Std.Format.text s!"⟨{h.real_part}, {h.epsilon_part}, {h.infinite_part}, {h.exceptional}⟩"


-- /-- Natural embedding `ℚ → ℚ*`. -/
-- -- def ofReal : (x:ℚ) → ℚ⋆ := Hyper.mk x 0 0
-- @[coe] -- coercion from reals to hyperreals
-- def ofReal (x : ℚ) : ℚ⋆ := Hyper.mk x 0 0

-- @[coe]
-- def ofNat (x : Nat) : ℚ⋆ := Hyper.mk x 0 0
-- -- e.g. 0 => 0 + 0ε + 0ω


instance : OfNat Hyper 0 where
  ofNat := Zero.zero

instance : OfNat Hyper 1 where
  ofNat := One.one

instance : OfNat Hyper x where
  ofNat := Hyper.mk (x : ℚ) 0 0 0


-- Boolean equality of hyperreals
-- noncomputable -- because it depends on 'Real.decidableEq', and it does not have executable code
-- instance : BEq Hyper :=
--   ⟨fun x y => x.real_part == y.real_part && x.epsilon_part == y.epsilon_part && x.infinite_part == y.infinite_part⟩

-- Decidable equality of hyperreals
-- noncomputable -- because it depends on 'Real.decidableEq', and it does not have executable code
-- instance : DecidableEq Hyper :=
--   fun x y =>
--     if h1 : x.real_part = y.real_part then
--       if h2 : x.epsilon_part = y.epsilon_part then
--         if h3 : x.infinite_part = y.infinite_part then
--           isTrue ⟨h1, h2, h3⟩
--         else
--           isFalse (fun h => Hyper.noConfusion h (fun h1 h2 h3 => h3 h3))
--       else
--         isFalse (fun h => Hyper.noConfusion h (fun h1 h2 h3 => h2 h2))
--     else
--       isFalse (fun h => Hyper.noConfusion h (fun h1 h2 h3 => h1 h1))



noncomputable
instance : DecidableEq Hyper :=
  λ x y => if
    x.real_part = y.real_part ∧ x.epsilon_part = y.epsilon_part ∧ x.infinite_part = y.infinite_part ∧ x.exceptional = y.exceptional
  then isTrue sorry else isFalse sorry

-- unfold Mul.mul instead of Hyper.mul NEVER HELPS :(
-- unfold Mul.mul at product  -- Explicitly unfold multiplication at 'product'  e.g. let product := (0 : Hyper) * (a:Hyper)
instance : Mul Hyper where
  mul x y :=
    ⟨ x.real_part * y.real_part + x.epsilon_part * y.infinite_part + x.infinite_part * y.epsilon_part,
      x.real_part * y.epsilon_part + x.epsilon_part * y.real_part,
      x.real_part * y.infinite_part + x.infinite_part * y.real_part,
     ( x.exceptional || y.exceptional
    || x.epsilon_part ≠ 0 && y.epsilon_part ≠ 0
    || x.infinite_part ≠ 0 && y.infinite_part ≠ 0
    ) -- && (x.real_part ≠ 0 &&  y.real_part ≠ 0) hack for 0*x=0
      ⟩

axiom hyper_gauged : Hyper -> ε * ω = 1  -- no need for axiom, it's a lemma following the definition of mul

-- Explicitly stating HMul might help if Lean does not infer it automatically
instance : HMul Hyper Hyper Hyper where
  hMul := Mul.mul

instance : HSMul ℤ Hyper Hyper where
  hSMul z a := ⟨z * a.real_part, z * a.epsilon_part, z * a.infinite_part, a.exceptional && z ≠ 0⟩

--  HSMul.hSMul high speed multiplication z × Hyper → Hyper
instance : HSMul ℤ Hyper Hyper where
  hSMul z a := ⟨z * a.real_part, z * a.epsilon_part, z * a.infinite_part, a.exceptional && z ≠ 0⟩
--   hSMul z a := z * a OUR Hyper ACTS LIKE SCALAR! use normal mul ℚ⋆ × Hyper → Hyper

instance : HSMul ℚ Hyper Hyper where
  hSMul q a := ⟨q * a.real_part, q * a.epsilon_part, q * a.infinite_part, a.exceptional && q ≠ 0⟩
  -- hSMul z a := z * a

instance : HSMul ℕ Hyper Hyper where
  hSMul n a := ⟨n * a.real_part, n * a.epsilon_part, n * a.infinite_part, a.exceptional && n ≠ 0⟩
  -- hSMul z a := z * a

instance : HSMul ℚ≥0 Hyper Hyper where
  hSMul q a := ⟨q * a.real_part, q * a.epsilon_part, q * a.infinite_part, a.exceptional && q ≠ 0⟩
  -- hSMul z a := (z:ℚ⋆) * a


-- Define the instance of OfNat for Hyper

-- instance : OfReal Hyper x where
--   ofNat := Hyper.mk (x : ℚ) 0 0

def maxFloat : Float := 1.7976931348623157e+308

-- all noncomputable mess up the whole pipeline
-- noncomputable -- why not? because we can't even decide x.real_part ≠ 0 in finite time could be ≠0 at position 10^100000
-- noncomputable -- why not? "because it depends on 'Real.instLinearOrderedField'"
-- noncomputable -- why not? it does not have executable code
instance : Inv Hyper where  -- Inv.inv
  inv (x:Hyper) := ⟨1/x.real_part, 1/x.infinite_part, 1/x.epsilon_part, x.exceptional⟩


    -- if x == 0 then 0 -- The inverse of 0 is 0 by convention. !?!?
    -- -- else if x.exception then x -- NaN or ε² or ±∞
    -- else if x.real_part ≠ 0 ∧ x.epsilon_part ≠ 0 ∧ x.infinite_part ≠ 0 then
    --  ⟨1/x.real_part, 1/x.infinite_part, 1/x.epsilon_part, x.exception⟩ -- ε and ω are swapped!
    -- else if x.real_part ≠ 0 ∧ x.epsilon_part ≠ 0 then ⟨1 / x.real_part, 0, 1/ x.epsilon_part, x.exception⟩
    -- else if x.real_part ≠ 0 ∧ x.infinite_part ≠ 0 then ⟨1 / x.real_part, 1 / x.infinite_part, 0, x.exception⟩
    -- else if x.real_part ≠ 0 then ⟨1 / x.real_part, 0, 0 , x.exception⟩
    -- else if x.epsilon_part ≠ 0 ∧ x.infinite_part ≠ 0 then ⟨0, 1/x.infinite_part, 1/x.epsilon_part, x.exception⟩
    -- else if x.infinite_part ≠ 0 then ⟨0, 1/x.infinite_part, 0, x.exception⟩
    -- else if x.epsilon_part ≠ 0 then ⟨0, 0, 1/x.epsilon_part, x.exception⟩
    -- else ⟨0, 0, 100000000, x.exception⟩ -- Need proper handling of 0 division
    -- -- else ⟨∞, 0, 0⟩ -- Need proper handling of 0 division

-- noncomputable
instance : Div Hyper where
  div x y := x * y⁻¹ -- via inverse

-- instance : Field (GaloisField p n) :=
--   inferInstanceAs (Field (SplittingField _))
-- variables {p : ℕ} [fact p.prime]
-- instance : field (ℚ_[p]) := Cauchy.field

-- instance : Field Hyper := by apply_instance -- unknown tactic

@[ext] -- make extension theorem for Hyper available via ext keyword instead of "apply Hyper.ext"
lemma Hyper.ext : ∀ (x y : Hyper), x.real_part = y.real_part → x.epsilon_part = y.epsilon_part → x.infinite_part = y.infinite_part → x.exceptional = y.exceptional → x = y
  :=
  fun x y =>
    match x, y with
    | ⟨xr, xe, xi, xx⟩, ⟨yr, ye, yi, yx⟩ =>
      fun (h₁ : xr = yr) (h₂ : xe = ye) (h₃ : xi = yi) (h₄ : xx = yx)=>
        match h₁, h₂, h₃, h₄ with
        | rfl, rfl, rfl, rfl => rfl

theorem false_or_a_eq_ax (a : Prop) : false ∨ a = a :=
  Or.inr rfl


theorem false_or_a_eq_ax0 (a : Bool) : false ∨ a = a :=
  Or.inr rfl


theorem false_or_a_eq_a (a : Prop) : False ∨ a = a :=
  Or.inr rfl


theorem false_or_a_eq_a0 (a : Bool) : False ∨ a = a :=
  Or.inr rfl


theorem false_or_a_eq_a1 (a : Boolean) : False ∨ a = a :=
  Or.inr rfl


theorem false_or_exception_eq (a : Hyper) : False ∨ a.exceptional = a.exceptional :=
  Or.inr rfl



-- theorem zero_keeps_exception : ∀ ( a : ℚ⋆) : (0 + a).exception = a.exception :=
--   λ a => show (zeroHyper + a).exception = a.exception, from
--     rfl  -- Since adding false (zeroHyper.exception) does not change a.exception
  -- let sum:=(0 + a)
  -- sorry
  -- have h : sum.exception = a.exception := by
  --   exact false_or_exception_eq a
  -- Or.inr rfl

-- theorem zero_keeps_exception (a : Hyper) : (zeroHyper + a).exception = a.exception :=
--   by simp [Zero.zero, Add.add, or_false]

-- theorem zero_keeps_exception (a : Hyper) : (zeroHyper + a).exception = a.exception :=
--   show (false ∨ a.exception) = a.exception, from
--     eq_true_intro (or_false a.exception)

-- lemma bla (a : Hyper) : false = true ∨ a.exception = a.exception := by
--   exact Or.inr rfl


-- lemma hyper_zero_add (a : Hyper) : 0 + a = a := by
-- lemma hyper_zero0R_add (a : Hyper) : (0:ℚ) + a = a := by
--   apply Hyper.ext
--   { show 0 + a.real_part = a.real_part; ring }
--   { show 0 + a.epsilon_part = a.epsilon_part; ring }
--   { show 0 + a.infinite_part = a.infinite_part; ring }
--   -- { show (false ∨ a.exception) = a.exception;  simp [or_false]} -- ok for PROP
--   { show (false || a.exception) = a.exception;  simp [or_false]} -- NOT ok for Bool
  -- in lean a ∨ b = c is parsed as a ∨ (b = c) !!!
  -- Or.inr rfl   only applies to pattern a ∨ (b = b)  OK got it

lemma real_part_zero_is_0: Hyper.real_part 0 = 0 := by
  rfl

lemma hyper_coercion_0: (0:ℚ) = (0:ℚ⋆) := by
  rfl

lemma hyper_coercion_1: (1:ℚ) = (1:ℚ⋆) := by
  rfl

lemma hyper_coercion_nat0: 0 = (0:ℚ⋆) := by
  rfl

-- lemma hyper_coercion_nat: 0 = (0:ℚ⋆) := by
--   -- #check Coe (ℕ → ℚ) -- Checks if there is a coercion from ℕ to ℚ  -- OK via Sort types
--   -- #check Coe (ℚ → ℚ⋆) -- Checks if there is a coercion from ℚ to ℚ⋆
--   have coerce: (0 : ℕ) = (0: ℚ ) := by
--     simp
--   rw [coerce]
--   rfl


lemma hyper_add_zero (a : Hyper) : a + 0 = a := by
  -- apply Hyper.ext
  ext
  { show a.real_part + 0 = a.real_part; ring }
  { show a.epsilon_part + 0 = a.epsilon_part; ring }
  { show a.infinite_part + 0 = a.infinite_part; ring }
  -- { show (a.exception ∨ false ) = a.exception;  simp [or_false]} -- OK for PROP
  { show (a.exceptional || false ) = a.exceptional;  simp [or_false]}



/--using: instance : Add Hyper := ⟨
  λ x y => ⟨x.real_part + y.real_part, x.epsilon_part + y.epsilon_part, x.infinite_part + y.infinite_part⟩
⟩-/
lemma hyper_zero_add (a : Hyper) : 0 + a = a := by
  apply Hyper.ext
  -- type_check 0 -- ?_uniq.15119 instead of Zero.zero
  -- type_check a
  -- don't do nothing: dsimp [Add.add]; ring_nf;
  { show Hyper.real_part 0 + a.real_part = a.real_part
    rw [real_part_zero_is_0]
    ring
  }
  { show 0 + a.epsilon_part = a.epsilon_part; ring }
  { show 0 + a.infinite_part = a.infinite_part; ring }
  -- { show (false ∨ a.exception) = a.exception;  simp [or_false]}
  { show (false || a.exceptional) = a.exceptional;  simp [or_false]}
  -- calc syntax is VERY FINICKY! it does NOT need := by  this syntax is ok but doen't work:
  --  { show Hyper.real_part 0 + a.real_part = a.real_part from
  --    calc
  --       Hyper.real_part 0 + a.real_part = 0 + a.real_part : by rw [real_part_zero_is_0] |
  --       _ = a.real_part
  --   }



--  same thing?
-- lemma hyper_zero0H_add (a : Hyper) : (0: Hyper) + a = a := by



-- lemma hyper_add_zero0 (a : Hyper) : a + (0:ℚ) = a := by
--   apply Hyper.ext
--   { show a.real_part + 0 = a.real_part; ring }
--   { show a.epsilon_part + 0 = a.epsilon_part; ring }
--   { show a.infinite_part + 0 = a.infinite_part; ring }
--   -- { show (a.exception ∨ false ) = a.exception;  simp [or_false]}
--   { show (a.exceptional || false ) = a.exceptional;  simp [or_false]}


lemma aorb (a b : Bool) : a || b = b || a := by
  simp [or_comm]

lemma aorb1 (a b : Bool) : (a || b) = (b || a) := by
  simp [Bool.or_comm]

lemma hyper_add_comm (a b : Hyper) : a + b = b + a := by
  apply Hyper.ext
  { show a.real_part + b.real_part = b.real_part + a.real_part; ring }
  { show a.epsilon_part + b.epsilon_part = b.epsilon_part + a.epsilon_part; ring }
  { show a.infinite_part + b.infinite_part = b.infinite_part + a.infinite_part; ring }
  { show (a.exceptional || b.exceptional) = (b.exceptional || a.exceptional);  simp [Bool.or_comm]}
  -- { show (a.exception ∨ b.exception) = (b.exception ∨ a.exception);  simp [or_comm]} -- for Prop


lemma hyper_add_assoc (a b c : Hyper) : a + b + c = a + (b + c) := by
  apply Hyper.ext
  { show a.real_part + b.real_part + c.real_part = a.real_part + (b.real_part + c.real_part); ring }
  { show a.epsilon_part + b.epsilon_part + c.epsilon_part = a.epsilon_part + (b.epsilon_part + c.epsilon_part); ring }
  { show a.infinite_part + b.infinite_part + c.infinite_part = a.infinite_part + (b.infinite_part + c.infinite_part); ring }
  { show ((a.exceptional || b.exceptional) || c.exceptional) = (a.exceptional || (b.exceptional || c.exceptional));  simp [Bool.or_assoc]}
  -- { show ((a.exception ∨ b.exception) ∨ c.exception) = (a.exception ∨ (b.exception ∨ c.exception));  simp [or_assoc]}



lemma hyper_add_left_neg (a : Hyper) : -a + a = 0 := by
  apply Hyper.ext
  { show -a.real_part + a.real_part = 0; ring }
  { show -a.epsilon_part + a.epsilon_part = 0; ring }
  { show -a.infinite_part + a.infinite_part = 0; ring }
  { show ((-a).exceptional || a.exceptional) = false; sorry } -- todo COULD BE TRUE NaN + NaN = NaN !
  -- { show ((-a).exception ∨ a.exception) = false; sorry } -- todo COULD BE TRUE NaN + NaN = NaN !

-- lemma hyper_zero_is_zero :  (0:ℚ⋆) = (0:ℚ) := by
--   rfl

lemma zero_times_anything: (0:ℚ) * (a : ℚ) + (0:ℚ) * (b : ℚ) = 0 := by
  ring

-- lemma zero_times_anything0: (0:ℚ) * (a : ℚ) + (0:ℚ) * (b : ℚ) = (0:ℚ⋆) := by
--   let left := (0:ℚ) * (a : ℚ) + (0:ℚ) * (b : ℚ)
--   let right := (0:ℚ⋆)
--   rw [hyper_zero_is_zero]
--   have right_ok: right = 0 := by apply hyper_zero_is_zero
--   -- apply right_ok
--   -- show (0:ℚ) * (a : ℚ) + (0:ℚ) * (b : ℚ) = 0
--   -- rw [zero_times_anything]
--   -- ring
--   rw [right_ok]
  -- exact zero_times_anything

-- lemma zero_times_anything0part: (0:ℚ) * (a : ℚ) + (0:ℚ) * (b : ℚ) = Hyper.real_part 0 := by
  -- let right := Hyper.real_part 0
  -- have h : right = 0 := by
  --   rfl
  -- show right = 0
  -- {sorry}
  -- ring

-- lemma zero_times_anything0epart: (0:ℚ) * (a : ℚ) + (0:ℚ) * (b : ℚ) = Hyper.epsilon_part 0 := by
--   sorry

-- lemma hyper_zero_mul0 (a : Hyper) : 0 * a = 0 := by

lemma hyper_real_part_one_is_1: (1:Hyper).real_part = 1 := by
  rfl

lemma hyper_real_part_zero_is_0: (0:Hyper).real_part = 0 := by
  rfl

-- lemma hyper_real_part_zero_is_zero: Hyper.real_part (0:Hyper) = (0:ℚ) := by
--   rfl

-- lemma hyper_real_part_one_is_one: Hyper.real_part 1 = (1:ℚ) := by
--   rfl

lemma hyper_product(a:Hyper): (0*a).real_part = 0 * a.real_part + 0 * a.infinite_part + 0 * a.epsilon_part  := by
  -- let mu := (0*a)
  -- unfold Mul.mul at mu
  rfl

-- lemma hyper_zero_0_part: (0 * (a:Hyper)).real_part = 0 := by
lemma hyper_zero_0_part: ((0:Hyper) * (a:Hyper)).real_part = 0 := by
  -- let product := (0 : Hyper) * (a:Hyper)
  -- unfold Mul.mul at product  -- Explicitly unfold multiplication at 'product'
  rw [hyper_product a]
  show 0 * a.real_part + 0 * a.infinite_part + 0 * a.epsilon_part = 0
  ring



lemma hyper_zero_mul (a : Hyper) : 0 * a = 0 := by
  -- let mu := (0:Hyper) * a
  -- unfold Mul.mul at mu
  apply Hyper.ext
  { show 0 * a.real_part + 0 * a.infinite_part + 0 * a.epsilon_part = 0; ring }
  { show 0 * a.epsilon_part + 0 * a.real_part = 0; ring }
  { show 0 * a.infinite_part + 0 * a.real_part = 0; ring }
  { sorry } -- todo 0 * NaN = NaN! OK! 😺

/--
      x.exceptional || y.exceptional -- for Bool
    || x.epsilon_part ≠ 0 && y.epsilon_part ≠ 0
    || x.infinite_part ≠ 0 && y.infinite_part ≠ 0
-/

lemma hyper_one_mul (a : Hyper) : 1 * a = a := by
  apply Hyper.ext
  { show 1 * a.real_part + 0 * a.infinite_part + 0 * a.epsilon_part = a.real_part; ring }
  { show 1 * a.epsilon_part + 0 * a.real_part = a.epsilon_part; ring }
  { show 1 * a.infinite_part + 0 * a.real_part = a.infinite_part; ring }
  { show (false || a.exceptional
    || 0 ≠ 0 && a.epsilon_part ≠ 0
    || 0 ≠ 0 && a.infinite_part ≠ 0)
    = a.exceptional;  simp [false_or] }


lemma hyper_mul_zero (a : Hyper) : a * 0 = 0 := by
  apply Hyper.ext
  { show a.real_part * 0 + a.epsilon_part * 0 + a.infinite_part * 0 = 0; ring }
  { show a.real_part * 0 + a.epsilon_part * 0 = 0; ring }
  { show a.real_part * 0 + a.infinite_part * 0 = 0; ring }
  { show (a.exceptional || false
    || a.epsilon_part ≠ 0 && 0 ≠ 0
    || a.infinite_part ≠ 0 && 0 ≠ 0 )
    = false;  simp [or_false]; sorry } -- todo NaN * 0 = NaN! OK! 😺

lemma hyper_mul_one (a : Hyper) : a * 1 = a := by
  apply Hyper.ext
  { show a.real_part * 1 + a.epsilon_part * 0 + a.infinite_part *0 = a.real_part ; ring }
  { show a.real_part * 0 + a.epsilon_part * 1 = a.epsilon_part; ring }
  { show a.real_part * 0 + a.infinite_part * 1 = a.infinite_part; ring }
  { show (a.exceptional || false
    || a.epsilon_part ≠ 0 && 0 ≠ 0
    || a.infinite_part ≠ 0 && 0 ≠ 0 )
    = a.exceptional;  simp [or_false] }

lemma exists_pair_ne : ∃ (a b : Hyper), a ≠ b := by
  use 0
  use 1
  have h : (0:Hyper) ≠ (1:Hyper) := by
    intro h
    have h1 : (0:Hyper).real_part = (1:Hyper).real_part := by
      rw [h]
    simp [Zero.zero, One.one] at h1
    have : 0 = 1 := h1
    exact absurd this (ne_of_lt (by norm_num)) -- (by decide)
  exact h

-- THIS CANNOT BE DONE currently because of the complicated way the inverse is defined
-- THIS CANNOT BE DONE currently because multiplication and inverse don't cancel out ;)
lemma hyper_inv_cancel (a : Hyper) (h : a ≠ 0) : a * a⁻¹ = 1 := by
  sorry

--   inv (x:Hyper) :=
--     if x == 0 then 0 -- The inverse of 0 is 0 by convention. !?!?
theorem hyper_inv_zero : (0 : Hyper)⁻¹ = 0 := by
  apply Hyper.ext
  { show 1 / 0 = 0 ; rfl }
  { show 1 / 0 = 0 ; rfl }
  { show 1 / 0 = 0 ; rfl }
  { show false = false ; rfl  }



lemma hyper_mul_comm (a b : Hyper) : a * b = b * a := by
  apply Hyper.ext
  { show a.real_part * b.real_part + a.epsilon_part * b.infinite_part + a.infinite_part * b.epsilon_part = b.real_part * a.real_part + b.epsilon_part * a.infinite_part + b.infinite_part * a.epsilon_part; ring }
  { show a.real_part * b.epsilon_part + a.epsilon_part * b.real_part = b.real_part * a.epsilon_part + b.epsilon_part * a.real_part; ring }
  { show a.real_part * b.infinite_part + a.infinite_part * b.real_part = b.real_part * a.infinite_part + b.infinite_part * a.real_part; ring }
  -- { show (a.exceptional || b.exceptional) = (b.exceptional || a.exceptional);  simp [Bool.or_comm]}
  { show ( (a.exceptional || b.exceptional)
    || (a.epsilon_part ≠ 0 && b.epsilon_part ≠ 0)
    || (a.infinite_part ≠ 0 && b.infinite_part ≠ 0)
    ) = (
    (b.exceptional || a.exceptional)
    || (b.epsilon_part ≠ 0 && a.epsilon_part ≠ 0)
    || (b.infinite_part ≠ 0 && a.infinite_part ≠ 0)
    );
    simp [Bool.or_comm, Bool.and_comm]
    }
  -- UFF, OK! 😺




-- instance : Mul Hyper where
--   mul x y :=
--     ⟨ x.r * y.r + x.e * y.i + x.i * y.e,
--       x.r * y.e + x.e * y.r,
--       x.r * y.i + x.i * y.r,
--       x.exceptional || y.exceptional
--     || x.e ≠ 0 && y.e ≠ 0
--     || x.i ≠ 0 && y.i ≠ 0
--       ⟩



lemma hyper_left_distrib (a b c : Hyper) : a * (b + c) = a * b + a * c := by
  let left := a * (b + c)
  let summe := (b + c)
  let right := a * b + a * c

  unfold Mul.mul at left
  unfold Mul.mul at right
  unfold Add.add at summe
  let ar := a.real_part
  let ae := a.epsilon_part
  let ai := a.infinite_part
  let ax := a.exceptional
  let br := b.real_part
  let be := b.epsilon_part
  let bi := b.infinite_part
  let bx := b.exceptional
  let cr := c.real_part
  let ce := c.epsilon_part
  let ci := c.infinite_part
  let cx := c.exceptional

  apply Hyper.ext
  -- a * (b + c) = a * b + a * c
  {
    sorry
    -- { show a.real_part * ( b.real_part + c.real_part) +
    -- + … + a.epsilon_part * b.infinite_part + a.infinite_part * b.epsilon_part = b.real_part * a.real_part + b.epsilon_part * a.infinite_part + b.infinite_part * a.epsilon_part; ring }
  }
  -- {
  -- -- a * (b + c) = a * b + a * c
  --   show (a * (b + c)).real_part = (a * b + a * c).real_part
  --   calc
  --         (a * (b + c)).real_part = (a * (b + c)).real_part := by rfl
  --     _ = (a * ⟨ br + cr , be + ce , bi + ci ⟩ ).real_part := by rfl
  --   _ = ar * br + ar * cr + ae * bi + ae * ci + ai * be + ai * ce := by sorry
  --   _ = ar * br + ae * bi + ai * be + ar * cr + ae * ci + ai * ce := by rw [add_comm, add_assoc]
  --   _ = (ar * br + ae * bi + ai * be) + (ar * cr + ae * ci + ai * ce) := by sorry
  --   _ = (a * b).real_part + (a * c).real_part := by sorry
  --   _ = (a * b + a * c).real_part := by sorry
  -- }
  -- {
  --   show (a * (b + c)).epsilon_part = (a * b + a * c).epsilon_part
  --   sorry
  -- }
  {
    show (a * (b + c)).infinite_part = (a * b + a * c).infinite_part
    sorry
  }
  {
    show (a * (b + c)).exceptional = (a * b + a * c).exceptional
    sorry
  }
  -- { show ar * (bi + ci) + ai * (br + cr) = ar * bi + ai * br + ar * ci + ai * cr; ring }



lemma hyper_mul_assoc (a b c : Hyper) : a * b * c = a * (b * c) := by
  let left := a * b * c
  let right := a * (b * c)
  unfold Mul.mul at left
  unfold Mul.mul at right
  have right_is: right = a.real_part * b.real_part * c.real_part + a.epsilon_part * b.infinite_part * c.infinite_part := by sorry
  apply Hyper.ext
  {sorry}
  {sorry}
  {sorry}
  {sorry}



lemma hyper_right_distrib (a b c : Hyper) : (a + b) * c = a * c + b * c := by
  apply Hyper.ext
  {sorry}
  {sorry}
  {sorry}
  {sorry}



lemma zero_ne_one (h : (0:Hyper) = 1) : False := by
  have h1 : (0:Hyper).real_part = (1:Hyper).real_part := by
    rw [h]
  simp [Zero.zero, One.one] at h1
  -- The above simplification leads to 0 = 1 in real numbers, which is a contradiction
  -- rw [hyper_real_part_zero_is_zero, hyper_real_part_one_is_one] at h1
  -- contradiction
  have : 0 = 1 := h1
  -- have : (0:ℚ) = (1:ℚ) := h1
  -- This is a clear contradiction as 0.0 ≠ 1.0
  exact absurd this (ne_of_lt (by norm_num)) -- (by decide)

-- lemma hyper_nsmul_like_mul (x : ℚ⋆) : 0 • x = 0 :=
--   rfl

-- lemma hyper_nsmul_like_mul (a : ℕ) (x : ℚ⋆) : a • x = a * x :=
--   rfl

lemma hyper_hsmul_like_mul (a : ℚ⋆) (x : ℚ⋆) : a • x = a * x :=
  rfl



noncomputable -- because it depends on 'Real.instLinearOrderedField', and it does not have executable code
-- instance : LinearOrderedField Hyper := {
instance : Field Hyper := {
  mul := Mul.mul,
  add := Add.add,
  neg := Neg.neg,
  inv := Inv.inv,
  zero := 0, -- Zero.zero,
  one := 1, -- One.one,
   -- include proofs showing these satisfy field axioms
  zero_add := hyper_zero_add,
  zero_mul := hyper_zero_mul,
  one_mul:= hyper_one_mul,
  mul_one:= hyper_mul_one,
  mul_zero:= hyper_mul_zero,
  add_assoc := hyper_add_assoc,
  add_zero := hyper_add_zero,
  add_left_neg:= hyper_add_left_neg,
  add_comm:= hyper_add_comm,
  mul_assoc:= hyper_mul_assoc,
  mul_inv_cancel:= hyper_inv_cancel, -- violated by ϵ*ϵ=0 since ϵ=ϵ⋅ϵ⋅ϵ−1=0⋅ϵ−1=0 but ϵ≠0
  mul_comm:= hyper_mul_comm,
  inv_zero:=  hyper_inv_zero, -- (0:Hyper)⁻¹ = 0, The inverse of 0 is 0 by convention. !?!?
  left_distrib:= hyper_left_distrib,
  right_distrib:= hyper_right_distrib,
  nsmul:= HSMul.hSMul,
  -- nsmul:= (HSMul.hSMul, hyper_nsmul_like_mul),
  zsmul:= HSMul.hSMul,
  qsmul:= HSMul.hSMul,
  nnqsmul:= HSMul.hSMul, -- (· • ·)
  exists_pair_ne:=⟨ 0 , 1 , zero_ne_one ⟩,
}
  /--
  -- The hyperreal numbers ℚ⋆ form a linear ordered field.
  le := sorry,
  lt := sorry,
  le_refl := sorry,
  le_trans := sorry,
  lt_iff_le_not_le := sorry,
  le_antisymm := sorry,
  add_le_add_left := sorry,
  zero_le_one := sorry,
  mul_pos := sorry,
  le_total:=sorry,
  decidableLE := sorry,
  -- decidable_le := sorry,
  -- decidable_eq := sorry,
  -- decidable_lt := sorry
  -/



lemma epsilon_times_omega_is_one : ε * ω = 1 := by
  apply Hyper.ext
  { show 0 * 0 + 1 * 1 + 0 * 0 = 1; ring }
  { show 0 * 0 + 1 * 0 = 0; ring }
  { show 0 * 1 + 0 * 0 = 0; ring }
  { show false = false; rfl }

lemma omega_times_epsilon_is_one : ω * ε  = 1 := by
  apply Hyper.ext
  { show 0 * 0 + 0 * 0 + 1 * 1  = 1; ring }
  { show 0 * 1 + 0 * 0 = 0; ring }
  { show 0 * 0 + 1 * 0 = 0; ring }
  { show false = false; rfl }


lemma omega_times_omega_is_ZERO : ω * ω  = ω² := by
  apply Hyper.ext
  { show 0 * 0 + 0 * 1 + 1 * 0  = 0; ring }
  { show 0 * 0 + 0 * 0 = 0; ring }
  { show 0 * 1 + 1 * 0 = 1; sorry } -- todo currently ω * ω = ε² ≈ NaN
  { show (false = false
  || 0 ≠ 0 && 0 ≠ 0
  || 1 ≠ 0 && 1 ≠ 0) = true; rfl }


lemma epsilon_times_epsilon_is_ZERO : ε * ε = ε² := by
  apply Hyper.ext
  { show 0 * 0 + 1 * 0 + 0 * 1  = 0; ring }
  { show 0 * 1 + 1 * 0 = 0; ring }
  -- { show 0 * 1 + 1 * 0 = 1; sorry } -- todo currently ε * ε ≈ NaN
  { show 0 * 0 + 0 * 0 = 0; ring }
  { show (false = false
  || 1 ≠ 0 && 1 ≠ 0
  || 0 ≠ 0 && 0 ≠ 0) = true; rfl }


lemma product_zero_means_arg_is_zero (a b : Hyper) (h : a * b = 0) :  a = 0 ∨ b = 0 := by
  exact mul_eq_zero.mp h  -- USE EXISTING FIELD THEORY for our Hyper! 😺
  -- HAHA, this cannot be true since ε * ε = 0 but ε ≠ 0 !!


#eval Hyper.mk 1 2 3 0
#eval Hyper.mk 1 2 3 0 + Hyper.mk 1 2 3 0
#eval Hyper.mk 1 2 3 0 * Hyper.mk 1 2 3 0 -- 1 + 6 + 6 = 13 as real part!
#eval Hyper.mk 0 0 1 0 * Hyper.mk 0 0 1 0
#eval Hyper.mk 1 0 1 0 * Hyper.mk 1 0 1 0
#eval Hyper.mk 1 2 3 0 / Hyper.mk 1 2 3 0
-- #eval Hyper.mk 1 2 3 0 * Hyper.mk 1 2 3 0


end HyperQ
end Hypers
