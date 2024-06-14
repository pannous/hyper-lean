-- import data.real.basic -- Import basic real number theory in LEAN 3
import Mathlib.Data.Real.Basic -- Import basic real number theory in LEAN 4
import Mathlib.Data.Real.Ereal -- ∞
import Mathlib.Data.Real.Hyperreal -- defined as hyperfilter germ
import Init.Data.Nat.Basic
import Init.Prelude
import Init.Control.Basic -- Import basic control structures in LEAN 4

notation "∞" => (⊤ : EReal)
notation "-∞" => (⊥ : EReal)
notation "ℝ∞" => EReal -- ℝ±∞   ℝinf

-- def Hyperreal : Type :=  Germ (hyperfilter ℕ : Filter ℕ) ℝ deriving Inhabited

namespace Hypers
section Hypers

-- Define the structure of hyperreal numbers
structure Hyper :=
  real_part : ℝ -- todo ℝ∞
  epsilon_part : ℝ -- ε-part
  infinite_part : ℝ -- ω-part
  -- higher orders ω² not implemented here => ε² = 0 and ω² = ∞
  -- deriving Repr not in lean 4

-- Outer and inner field extensions
structure HyperGeneral :=
  components : List (ℝ × ℤ) -- [(3, 0), (1, 1), (2, -2)] => 3 + ω + 2ε^2 -- note ε = ω⁻¹

structure HyperSimple := -- Not applicable for derivatives where we need x+ε ≠ x for ∂f(x)=(f(x+ε)-f(x))/ε   !
  components : ℝ × ℤ  -- ONE of (3, 0), (1, 1), (2, -2) … => 3 or ω or 2ε^2 -- note ε = ω⁻¹
  -- components : ℝ × ℝ  -- ONE of (3, 0), (1, 1), (2, -2) … => 3 or ω or 2ε^2 -- note ε = ω⁻¹

-- @[inherit_doc]
notation "ℝ⋆" => Hyper  -- type \ R \ star <tab> for ℝ⋆
-- notation "ℝ*" => Hyper -- may conflict with Lean 4 notation for hyperreals

instance : One Hyper where
  one := ⟨1, 0, 0⟩

-- Zero.zero
instance : Zero Hyper where
  zero := ⟨0, 0, 0⟩


-- def zero := Zero.zero -- Hyper := ⟨0, 0, 0⟩ -- Hyper.0
-- def one : Hyper := ⟨1, 0, 0⟩
def epsilon : Hyper := ⟨0, 1, 0⟩
def omega : Hyper := ⟨0, 0, 1⟩
-- def ε : Hyper := ⟨0, 1, 0⟩
-- def ω : Hyper := ⟨0, 0, 1⟩



-- scoped notation "0" => zero -- doesn't work "invalid atom"
-- notation "O" => zero
-- scoped notation "O" => Zero.zero
-- scoped notation "I" => One.one
scoped notation "ε" => epsilon
scoped notation "ω" => omega

-- coercion from reals to hyperreals
instance : Coe ℝ ℝ⋆ where
  coe r := Hyper.mk r 0 0

instance : Coe ℤ ℝ⋆ where
  coe r := Hyper.mk r 0 0


-- This instance already exists in Lean’s standard library, so you don’t need to redefine it.
-- instance : Coe ℕ ℝ⋆ where
  -- coe n := Nat.cast n --n.toReal
instance : Coe ℕ ℝ⋆ where
  -- coe (n:ℕ) : Hyper := ⟨ (OfNat.ofNat Real n) 0 0 ⟩
  coe (n:ℕ) : Hyper := ⟨ (n:ℝ), 0, 0 ⟩
  -- coe (n:ℕ) : Hyper := ⟨ n, 0, 0 ⟩
  -- coe r := Hyper.mk (Real.ofNat r) 0 0
  -- coe r := Hyper.mk (r:ℝ) 0 0
  -- coe r := Hyper.mk (Nat.cast r) 0 0
  -- coe r := Hyper.mk (Nat.cast (r:ℝ)) 0 0

instance : SMul ℝ ℝ⋆ where
  smul r x := ⟨r * x.real_part, r * x.epsilon_part, r * x.infinite_part⟩

instance : Neg Hyper where
  neg x :=
    ⟨-x.real_part, -x.epsilon_part, -x.infinite_part⟩


-- Addition and multiplication of hyperreals
instance : Add Hyper := ⟨
  λ x y => ⟨x.real_part + y.real_part, x.epsilon_part + y.epsilon_part, x.infinite_part + y.infinite_part⟩
⟩

instance : Sub Hyper where
  sub x y := x + (-y)


-- /-- Natural embedding `ℝ → ℝ*`. -/
-- -- def ofReal : (x:ℝ) → ℝ⋆ := Hyper.mk x 0 0
-- @[coe] -- coercion from reals to hyperreals
-- def ofReal (x : ℝ) : ℝ⋆ := Hyper.mk x 0 0

-- @[coe]
-- def ofNat (x : Nat) : ℝ⋆ := Hyper.mk x 0 0
-- -- e.g. 0 => 0 + 0ε + 0ω


instance : OfNat Hyper 0 where
  ofNat := Zero.zero

instance : OfNat Hyper 1 where
  ofNat := One.one

instance : OfNat Hyper x where
  ofNat := Hyper.mk (x : ℝ) 0 0

--  HSMul.hSMul
instance : HSMul ℤ Hyper Hyper where
  hSMul z a := ⟨(z:ℝ) * a.real_part, (z:ℝ) * a.epsilon_part, (z:ℝ) * a.infinite_part⟩

-- Define the instance of OfNat for Hyper

-- instance : OfReal Hyper x where
--   ofNat := Hyper.mk (x : ℝ) 0 0


-- noncomputable
-- instance : BEq Hyper :=
--   ⟨fun x y => x.real_part == y.real_part && x.epsilon_part == y.epsilon_part && x.infinite_part == y.infinite_part⟩

-- unfold Mul.mul instead of Hyper.mul
-- unfold Mul.mul at product  -- Explicitly unfold multiplication at 'product'  e.g. let product := (0 : Hyper) * (a:Hyper)
instance : Mul Hyper where
  mul x y :=
    ⟨ x.real_part * y.real_part + x.epsilon_part * y.infinite_part,
      x.real_part * y.epsilon_part + x.epsilon_part * y.real_part,
      x.real_part * y.infinite_part + x.infinite_part * y.real_part ⟩



def maxFloat : Float := 1.7976931348623157e+308

noncomputable -- why not??
instance : Inv Hyper where
  inv (x:Hyper) :=
    if x.real_part ≠ 0 ∧ x.epsilon_part ≠ 0 ∧ x.infinite_part ≠ 0 then
     ⟨1/x.real_part, 1/x.infinite_part, 1/x.epsilon_part⟩ -- ε and ω are swapped!
    else if x.real_part ≠ 0 ∧ x.epsilon_part ≠ 0 then ⟨1 / x.real_part, 0, 1/ x.epsilon_part⟩
    else if x.real_part ≠ 0 ∧ x.infinite_part ≠ 0 then ⟨1 / x.real_part, 1 / x.infinite_part, 0⟩
    else if x.real_part ≠ 0 then ⟨1 / x.real_part, 0, 0 ⟩
    else if x.epsilon_part ≠ 0 ∧ x.infinite_part ≠ 0 then ⟨0, 1/x.infinite_part, 1/x.epsilon_part⟩
    else if x.infinite_part ≠ 0 then ⟨0, 1/x.infinite_part, 0⟩
    else if x.epsilon_part ≠ 0 then ⟨0, 0, 1/x.epsilon_part⟩
    else ⟨0, 0, 100000000⟩ -- Need proper handling of 0 division
    -- else ⟨∞, 0, 0⟩ -- Need proper handling of 0 division

noncomputable
instance : Div Hyper where
  div x y := x * y⁻¹ -- via inverse

-- instance : Field (GaloisField p n) :=
--   inferInstanceAs (Field (SplittingField _))
-- variables {p : ℕ} [fact p.prime]
-- instance : field (ℚ_[p]) := Cauchy.field

-- instance : Field Hyper := by apply_instance -- unknown tactic


lemma Hyper.ext : ∀ (x y : Hyper), x.real_part = y.real_part → x.epsilon_part = y.epsilon_part → x.infinite_part = y.infinite_part → x = y
  :=
  fun x y =>
    match x, y with
    | ⟨xr, xe, xi⟩, ⟨yr, ye, yi⟩ =>
      fun (h₁ : xr = yr) (h₂ : xe = ye) (h₃ : xi = yi) =>
        match h₁, h₂, h₃ with
        | rfl, rfl, rfl => rfl


-- lemma hyper_zero_add (a : Hyper) : 0 + a = a := by
lemma hyper_zero0R_add (a : Hyper) : (0:ℝ) + a = a := by
--   { show 0 + 0 = 0; ring }
  apply Hyper.ext
  { show 0 + a.real_part = a.real_part; ring }
  { show 0 + a.epsilon_part = a.epsilon_part; ring }
  { show 0 + a.infinite_part = a.infinite_part; ring }

lemma real_part_zero_is_0: Hyper.real_part 0 = 0 := by
  -- simp [Zero.zero]
  show Hyper.real_part 0 = 0
  -- exact rfl
  -- trivial
  sorry -- obvious!


lemma hyper_coercion_0: (0:ℝ) = (0:ℝ⋆) := by
  rfl

lemma hyper_coercion_1: (1:ℝ) = (1:ℝ⋆) := by
  rfl


lemma hyper_coercion_nat0: 0 = (0:ℝ⋆) := by
  rfl

lemma hyper_coercion_nat: (0:ℕ) = (0:ℝ⋆) := by
  #check Coe (ℕ → ℝ) -- Checks if there is a coercion from ℕ to ℝ  -- OK via Sort types
  #check Coe (ℝ → ℝ⋆) -- Checks if there is a coercion from ℝ to ℝ⋆
  have coerce: (0 : ℕ) = (0: ℝ ) := by
    simp
  rw [coerce]
  rfl

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
  -- calc syntax is VERY FINICKY! it does NOT need := by  this syntax is ok but doen't work:
  --  { show Hyper.real_part 0 + a.real_part = a.real_part from
  --    calc
  --       Hyper.real_part 0 + a.real_part = 0 + a.real_part : by rw [real_part_zero_is_0] |
  --       _ = a.real_part
  --   }



--  same thing?
-- lemma hyper_zero0H_add (a : Hyper) : (0: Hyper) + a = a := by


lemma hyper_add_zero (a : Hyper) : a + 0 = a := by
  apply Hyper.ext
  { show a.real_part + 0 = a.real_part; ring }
  { show a.epsilon_part + 0 = a.epsilon_part; ring }
  { show a.infinite_part + 0 = a.infinite_part; ring }


lemma hyper_add_zero0 (a : Hyper) : a + (0:ℝ) = a := by
  apply Hyper.ext
  { show a.real_part + 0 = a.real_part; ring }
  { show a.epsilon_part + 0 = a.epsilon_part; ring }
  { show a.infinite_part + 0 = a.infinite_part; ring }


lemma hyper_add_assoc (a b c : Hyper) : a + b + c = a + (b + c) := by
  apply Hyper.ext
  { show a.real_part + b.real_part + c.real_part = a.real_part + (b.real_part + c.real_part); ring }
  { show a.epsilon_part + b.epsilon_part + c.epsilon_part = a.epsilon_part + (b.epsilon_part + c.epsilon_part); ring }
  { show a.infinite_part + b.infinite_part + c.infinite_part = a.infinite_part + (b.infinite_part + c.infinite_part); ring }

lemma hyper_add_comm (a b : Hyper) : a + b = b + a := by
  apply Hyper.ext
  { show a.real_part + b.real_part = b.real_part + a.real_part; ring }
  { show a.epsilon_part + b.epsilon_part = b.epsilon_part + a.epsilon_part; ring }
  { show a.infinite_part + b.infinite_part = b.infinite_part + a.infinite_part; ring }

lemma hyper_add_left_neg (a : Hyper) : -a + a = 0 := by
  apply Hyper.ext
  { show -a.real_part + a.real_part = 0; ring }
  { show -a.epsilon_part + a.epsilon_part = 0; ring }
  { show -a.infinite_part + a.infinite_part = 0; ring }

lemma hyper_zero_is_zero :  (0:ℝ⋆) = (0:ℝ) := by
  rfl

lemma zero_times_anything: (0:ℝ) * (a : ℝ) + (0:ℝ) * (b : ℝ) = 0 := by
  ring

-- lemma zero_times_anything0: (0:ℝ) * (a : ℝ) + (0:ℝ) * (b : ℝ) = (0:ℝ⋆) := by
--   let lhs := (0:ℝ) * (a : ℝ) + (0:ℝ) * (b : ℝ)
--   let rhs := (0:ℝ⋆)
--   rw [hyper_zero_is_zero]
--   have rhs_ok: rhs = 0 := by apply hyper_zero_is_zero
--   -- apply rhs_ok
--   -- show (0:ℝ) * (a : ℝ) + (0:ℝ) * (b : ℝ) = 0
--   -- rw [zero_times_anything]
--   -- ring
--   rw [rhs_ok]
  -- exact zero_times_anything

-- lemma zero_times_anything0part: (0:ℝ) * (a : ℝ) + (0:ℝ) * (b : ℝ) = Hyper.real_part 0 := by
  -- let rhs := Hyper.real_part 0
  -- have h : rhs = 0 := by
  --   rfl
  -- show rhs = 0
  -- {sorry}
  -- ring

-- lemma zero_times_anything0epart: (0:ℝ) * (a : ℝ) + (0:ℝ) * (b : ℝ) = Hyper.epsilon_part 0 := by
--   sorry

-- lemma hyper_zero_mul0 (a : Hyper) : 0 * a = 0 := by

lemma hyper_real_part_zero_is_0: (0:Hyper).real_part = 0 := by
  let no := (0:Hyper)
  unfold Zero.zero at no
  -- absurd no.real_part_ne_zero no.real_part_ne_zero
  -- have h : no.real_part = 0 := by
  -- show no = O
  show no.real_part = 0
  -- already
  -- assumption -- tactic 'assumption' failed
  admit -- I admit! ≈ sorry
  -- admit!
  -- aesop
  -- sorry
  -- rfl
  -- show 0 = (Hyper.mk 0 0 0)
  -- show (Hyper.mk 0 0 0).real_part = 0

lemma hyper_real_part_zero_is_00: Hyper.real_part 0 = 0 := by
  show Hyper.real_part 0 = 0
  rfl

lemma hyper_product(a:Hyper): (0*a).real_part = 0 * a.real_part + 0 * a.infinite_part := by
  let mu := (0*a)
  unfold Mul.mul at mu
  rfl

-- lemma hyper_zero_0_part: (0 * (a:Hyper)).real_part = 0 := by
lemma hyper_zero_0_part: ((0:Hyper) * (a:Hyper)).real_part = 0 := by
  let product := (0 : Hyper) * (a:Hyper)
  unfold Mul.mul at product  -- Explicitly unfold multiplication at 'product'
  rw [hyper_product a]
  show 0 * a.real_part + 0 * a.infinite_part = 0
  ring



lemma hyper_zero_mul (a : Hyper) : 0 * a = 0 := by
  let mu := (0:Hyper) * a
  unfold Mul.mul at mu
  apply Hyper.ext
  { show 0 * a.real_part + 0 * a.infinite_part = 0; ring }
  { show 0 * a.epsilon_part + 0 * a.real_part = 0; ring }
  { show 0 * a.infinite_part + 0 * a.real_part = 0; ring }

lemma hyper_one_mul (a : Hyper) : 1 * a = a := by
  apply Hyper.ext
  { show 1 * a.real_part + 0 * a.infinite_part = a.real_part; ring }
  { show 1 * a.epsilon_part + 0 * a.real_part = a.epsilon_part; ring }
  { show 1 * a.infinite_part + 0 * a.real_part = a.infinite_part; ring }

lemma hyper_mul_one (a : Hyper) : a * 1 = a := by
  apply Hyper.ext
  { show a.real_part * 1 + a.epsilon_part * 0 = a.real_part; ring }
  { show a.real_part * 0 + a.epsilon_part * 1 = a.epsilon_part; ring }
  { show a.real_part * 0 + a.infinite_part * 1 = a.infinite_part; ring }

lemma hyper_mul_zero (a : Hyper) : a * 0 = 0 := by
  let mu := a * (0:Hyper)
  unfold Mul.mul at mu
  apply Hyper.ext
  { show a.real_part * 0 + a.epsilon_part * 0 = 0; ring }
  { show a.real_part * 0 + a.epsilon_part * 0 = 0; ring }
  { show a.real_part * 0 + a.infinite_part * 0 = 0; ring }

--  SAME ^^
-- lemma hyper_0_mul (a : Hyper) : (0:Hyper) * a = (0:Hyper) := by

-- THIS CANNOT BE DONE currently because of the complicated way the inverse is defined
lemma hyper_inv_cancel (a : Hyper) (h : a ≠ 0) : a * a⁻¹ = 1 := by
  let lhs := a * a⁻¹
  let rhs := 1
  have h_real_part : lhs.real_part = rhs := by
    sorry
    -- show a.real_part * (1 / a.real_part) + a.epsilon_part * (1 / a.epsilon_part) = 1
  have h_epsilon_part : lhs.epsilon_part = 0 := by
    sorry
    -- show a.real_part * 0 + a.epsilon_part * 0 = 0
  have h_infinite_part : lhs.infinite_part = 0 := by
    sorry
    -- show a.real_part * 0 + a.infinite_part * 0 = 0
  apply Hyper.ext
  sorry
  -- exact h_real_part
  exact h_epsilon_part
  exact h_infinite_part

lemma hyper_inv_zero (a : Hyper) (h : a = 0) : a⁻¹ = 0 := by
  sorry

lemma hyper_mul_comm (a b : Hyper) : a * b = b * a := by
  apply Hyper.ext
  { show a.real_part * b.real_part + a.epsilon_part * b.infinite_part = b.real_part * a.real_part + b.epsilon_part * a.infinite_part; ring }
  { show a.real_part * b.epsilon_part + a.epsilon_part * b.real_part = b.real_part * a.epsilon_part + b.epsilon_part * a.real_part; ring }
  { show a.real_part * b.infinite_part + a.infinite_part * b.real_part = b.real_part * a.infinite_part + b.infinite_part * a.real_part; ring }

lemma hyper_mul_assoc (a b c : Hyper) : a * b * c = a * (b * c) := by
  let lhs := a * b * c
  unfold Mul.mul at lhs
  let rhs := a * (b * c)
  unfold Mul.mul at rhs
  -- have rhs_is: rhs = a.real_part * b.real_part * c.real_part + a.epsilon_part * b.infinite_part * c.infinite_part := by simp
  apply Hyper.ext
  {sorry}
  {sorry}
  {sorry}
  -- { show a.real_part * b.real_part * c.real_part + a.epsilon_part * b.infinite_part * c.infinite_part = a.real_part * (b.real_part * c.real_part + b.epsilon_part * c.infinite_part); ring }
  -- { show a.real_part * b.epsilon_part * c.real_part + a.epsilon_part * b.real_part * c.infinite_part = a.real_part * (b.epsilon_part * c.real_part + b.real_part * c.infinite_part); ring }
  -- { show a.real_part * b.infinite_part * c.real_part + a.infinite_part * b.real_part * c.infinite_part = a.real_part * (b.infinite_part * c.real_part + b.real_part * c.infinite_part); ring }
  -- { show a.real_part * b.real_part * c.real_part + a.epsilon_part * b.infinite_part * c.infinite_part = a.real_part * (b.real_part * c.real_part + b.epsilon_part * c.infinite_part); ring }
  -- { show a.real_part * b.epsilon_part * c.real_part + a.epsilon_part * b.real_part * c.infinite_part = a.real_part * (b.epsilon_part * c.real_part + b.real_part * c.infinite_part); ring }
  -- { show a.real_part * b.infinite_part * c.real_part + a.infinite_part * b.real_part * c.infinite_part = a.real_part * (b.infinite_part * c.real_part + b.real_part * c.infinite_part); ring }

lemma hyper_left_distrib (a b c : Hyper) : a * (b + c) = a * b + a * c := by
  apply Hyper.ext
  {sorry}
  {sorry}
  {sorry}
  -- { show a.real_part * (b.real_part + c.real_part) + a.epsilon_part * (b.infinite_part + c.infinite_part) = a.real_part * b.real_part + a.real_part * c.real_part + a.epsilon_part * b.infinite_part + a.epsilon_part * c.infinite_part; ring }
  -- { show a.real_part * (b.infinite_part + c.infinite_part) + a.epsilon_part * (b.real_part + c.real_part) = a.real_part * b.infinite_part + a.real_part * c.infinite_part + a.epsilon_part * b.real_part + a.epsilon_part * c.real_part; ring }
  -- { show a.real_part * (b.real_part + c.infinite_part) + a.infinite_part * (b.real_part + c.infinite_part) = a.real_part * b.real_part + a.real_part * c.infinite_part + a.infinite_part * b.real_part + a.infinite_part * c.infinite_part; ring }

-- def my_star_operation (x y : ℤ) : ℤ := x * y
-- infix:10 "⋆" => my_star_operation
-- infix:10 "•" => my_star_operation
-- #eval 3 ⋆ 4  -- Output will be 13

lemma hyper_zsmul (n : ℤ) (a : Hyper) : n • a = n * a := by
  let lhs := n • a
  let rhs := n * a
  unfold HSMul.hSMul at lhs
  unfold Mul.mul at rhs
  apply Hyper.ext
  { show n * a.real_part = n * a.real_part; ring }
  { show n • a.epsilon_part = n * a.epsilon_part; ring }
  { show n • a.infinite_part = n * a.infinite_part; ring }



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
  mul_inv_cancel:= hyper_inv_cancel,
  mul_comm:= hyper_mul_comm,
  inv_zero:= hyper_inv_zero,
  left_distrib:= hyper_left_distrib,
  right_distrib:= hyper_right_distrib,
  zsmul:= sorry,
  -- nsmul:=sorry,
  -- qsmul:=sorry,
  -- nnqsmul:=sorry,
  -- exists_pair_ne:=sorry,
}

/-- The hyperreal numbers ℝ⋆ form a linear ordered field. -/
noncomputable
instance : LinearOrderedField ℝ⋆ :=
{
  zero := O, -- 0
  one := I,
  neg := Neg.neg,
  add := Add.add,
  mul := Mul.mul,
  -- Provide proofs for these
  add_assoc := hyper_add_assoc,
  -- zero_add := λ a => sorry,
  -- add_zero := sorry,
  -- add_left_neg := sorry,
  -- add_comm := sorry,
  -- mul_assoc := sorry,
  -- one_mul := sorry,
  -- mul_one := sorry,
  -- left_distrib := sorry,
  -- right_distrib := sorry,
  -- mul_comm := sorry,
  -- inv := Inv.inv,
  -- div := Div.div,
  -- exists_pair_ne := sorry,
  -- mul_inv_cancel := sorry,
  -- inv_zero := sorry,
  -- le := sorry,
  -- lt := sorry,
  -- le_refl := sorry,
  -- le_trans := sorry,
  -- lt_iff_le_not_le := sorry,
  -- le_antisymm := sorry,
  -- add_le_add_left := sorry,
  -- zero_le_one := sorry,
  -- mul_pos := sorry,
  -- -- add_lt_add_left := sorry,
  -- -- decidable_le := sorry,
  -- -- decidable_eq := sorry,
  -- -- decidable_lt := sorry
  -- nsmul := sorry,
  -- zero_mul:=sorry,
  -- mul_zero:=sorry,
  -- zsmul:=sorry,
  -- le_total:=sorry,
  -- decidableLE:=sorry,
  -- nnqsmul:=sorry,
  -- qsmul:=sorry,
}
-/


lemma hyper_mul_comm (a b : Hyper) : a * b = b * a := by
  apply Hyper.ext
  {
    show a.real_part * b.real_part + a.epsilon_part * b.infinite_part = b.real_part * a.real_part + b.epsilon_part * a.infinite_part
    ring
  }
  {show a.real_part * b.epsilon_part + a.epsilon_part * b.real_part = b.real_part * a.epsilon_part + b.epsilon_part * a.real_part; ring}
  {show a.real_part * b.infinite_part + a.infinite_part * b.real_part = b.real_part * a.infinite_part + b.infinite_part * a.real_part; ring}



-- lemma Hyper.ext : ∀ (x y : Hyper), x.real_part = y.real_part → x.epsilon_part = y.epsilon_part → x.infinite_part = y.infinite_part → x = y :=
--   fun x y h1 h2 h3 =>
--     match x, y with
--     | ⟨xr, xe, xi⟩, ⟨yr, ye, yi⟩ =>
--       have h : xr = yr ∧ xe = ye ∧ xi = yi := by
--         split; assumption
--       match h with
--       | ⟨rfl, rfl, rfl⟩ => rfl



-- this simplifies the definition with setting ε^2 = 0 and ω^2 = ∞
-- better:
-- single ε-value and exponent, e.g. (1, 1) => ε ; (1, 2) => ε^2
-- (epsilon_part : ℝ × ℝ) -- ε-part
-- todo: enable ε^2 and ω^2 via tuples of reals and exponentiats
-- structure Hyper_Complicated :=
-- (real_part : ℝ)
-- -- multiple ε-values and exponents,  e.g. [(1, 1),(1, 2)] => ε+ε^2
-- (epsilon_part : List (ℝ × ℝ)) -- ε-parts
-- (infinite_part : List (ℝ × ℝ)) -- ω-parts


-- todo: make epsilon and omega infinitesimal and infinite respectively
-- todo: add axioms for ε and ω



-- two instances of the same type are the same if their components are the same
example : Hyper.mk 1 2 3 = Hyper.mk 1 2 3 := by
  rfl

example : Hyper.mk 1 2 3 = Hyper.mk 1 2 (2 + 1) := by
  apply Hyper.ext
  rfl  -- real_part is directly equal
  rfl  -- epsilon_part is directly equal
  norm_num

example : Hyper.mk 1 2 3 = Hyper.mk 1 2 (2 + 1) := by
  -- congruence very powerful!
  congr -- when f x = f y and you want to reduce it to x = y, here we have f = Hyper.mk
  norm_num

def h1 := Hyper.mk 1 2 3
def h2 := Hyper.mk 4 5 6


example : h1 + h2 = Hyper.mk 5 7 9 := by
  let lhs := h1 + h2
  let rhs := Hyper.mk 5 7 9
  have h_real_part : lhs.real_part = rhs.real_part := by
    show 1 + 4 = 5;
    norm_num
  have h_epsilon_part : lhs.epsilon_part = rhs.epsilon_part := by
    show 2 + 5 = 7
    norm_num
  have h_infinite_part : lhs.infinite_part = rhs.infinite_part := by
    show 3 + 6 = 9
    norm_num
  apply Hyper.ext
  exact h_real_part
  exact h_epsilon_part
  exact h_infinite_part
-- NOT NEEDED / WORKING:
--   cases h1,
--   cases h2,
-- intro h
-- cases h
-- split
-- all_goals { rfl }
--   simp only [Add.add, Hyper.add]
-- congr use when f x = f y and you want to reduce it to x = y, here we have f = Hyper.mk


-- lemma hyper_addition :
-- lemma hyper_addition (a b c d e f : ℕ) : auto coerced to:
lemma hyper_addition (a b c d e f : ℝ) :
  Hyper.mk a b c + Hyper.mk d e f = Hyper.mk (a + d) (b + e) (c + f) := by
  let lhs := Hyper.mk a b c + Hyper.mk d e f
  let rhs := Hyper.mk (a + d) (b + e) (c + f)
  have h_real_part : lhs.real_part = rhs.real_part := by
    show a + d = a + d
    norm_num
  have h_epsilon_part : lhs.epsilon_part = rhs.epsilon_part := by
    show b + e = b + e
    norm_num
  have h_infinite_part : lhs.infinite_part = rhs.infinite_part := by
    show c + f = c + f
    norm_num
  apply Hyper.ext
  exact h_real_part
  exact h_epsilon_part
  exact h_infinite_part

-- apply the lemma to prove an addition
example : Hyper.mk 1 2 3 + Hyper.mk 4 5 6 = Hyper.mk (1 + 4) (2 + 5) (3 + 6) := by
  apply hyper_addition

-- example : h1 + h2 = Hyper.mk 5 7 9 := by
--   apply hyper_addition -- CAN'T DO THIS

-- example : h1 + h2 = Hyper.mk 5 7 9 := by
--   have h := hyper_addition 1 2 3 4 5 6
--   rw [h] -- Can't do this
--   norm_num



def h01 := Hyper.mk 1 0 0
def h02 := Hyper.mk 0 1 0

-- Example to verify multiplication
example : h01 * h02 = Hyper.mk 0 1 0 := by
  apply Hyper.ext
  {show 1 * 0 + 0 * 0 = 0; norm_num}
  {show 1 * 1 + 0 * 0 = 1; norm_num}
  {show 1 * 0 + 0 * 0 = 0; norm_num}


-- The expected result of multiplying h1 and h2
def expected := Hyper.mk (1*4 + 2*6) (1*5 + 2*4) (1*6 + 3*4)

def example_hyper_mul : ℝ⋆ :=
  let a := Hyper.mk 1 2 3
  let b := Hyper.mk 4 5 6
  a * b

-- example : example_hyper_mul = ⟨1 * 4 + 2 * 6, 1 * 5 + 2 * 4, 1 * 6 + 3 * 4⟩ := by
example : example_hyper_mul = expected := by
-- example : example_hyper_mul = ⟨16, 13, 18⟩ := by
  let lhs := example_hyper_mul
  let rhs : Hyper := ⟨1 * 4 + 2 * 6, 1 * 5 + 2 * 4, 1 * 6 + 3 * 4⟩
  have h_real_part : lhs.real_part = rhs.real_part := by
    show 1 * 4 + 2 * 6 = 1 * 4 + 2 * 6
    norm_num
  have h_epsilon_part : lhs.epsilon_part = rhs.epsilon_part := by
    show 1 * 5 + 2 * 4 = 1 * 5 + 2 * 4
    norm_num
  have h_infinite_part : lhs.infinite_part = rhs.infinite_part := by
    show 1 * 6 + 3 * 4 = 1 * 6 + 3 * 4
    norm_num
  apply Hyper.ext
  exact h_real_part
  exact h_epsilon_part
  exact h_infinite_part


lemma hyper_multiplication (a b c d e f : ℝ) : (Hyper.mk a b c) * (Hyper.mk d e f) = Hyper.mk (a * d + b * f) (a * e + b * d) (a * f + c * d) := by
  -- Define the multiplication result step by step
  let lhs := (Hyper.mk a b c) * (Hyper.mk d e f)
  let rhs := Hyper.mk (a * d + b * f) (a * e + b * d) (a * f + c * d)
  have h_real_part : lhs.real_part = rhs.real_part := by
    show a * d + b * f = a * d + b * f
    rfl
  have h_epsilon_part : lhs.epsilon_part = rhs.epsilon_part := by
    show a * e + b * d = a * e + b * d
    rfl
  -- Show the infinite_part components are equal
  have h_infinite_part : lhs.infinite_part = rhs.infinite_part := by
    show a * f + c * d = a * f + c * d
    rfl
  -- Combine the equalities to show the overall equality

  apply Hyper.ext
  exact h_real_part
  exact h_epsilon_part
  exact h_infinite_part



lemma hyper_multiplication2 (a b c d e f) :
  (Hyper.mk a b c) * (Hyper.mk d e f) = Hyper.mk (a * d + b * f) (a * e + b * d) (a * f + c * d) := by
  apply Hyper.ext
  { show a * d + b * f = a * d + b * f; rfl } -- stupid show!
  { show a * e + b * d = a * e + b * d; rfl }
  { show a * f + c * d = a * f + c * d; rfl }


example : Hyper.mk 0 0 0 = Hyper.mk 0 0 0 := by
  rfl

example : Hyper.mk (x : ℝ) 0 0 = Hyper.mk (x : ℝ) 0 0 := by
  rfl


example : one * zero = zero := by
  apply Hyper.ext
  all_goals
  {
    show 1 * 0 + 0 * 0 = 0
    norm_num
  }


-- example : one * zero = zero := by
  -- apply hyper_multiplication(1 0 0 0 0 0)
-- Example using the coercion


example : (↑(0:ℝ) : ℝ⋆) = (zero : ℝ⋆) := by
  rfl -- works


-- Verify coercion from ℕ to ℝ⋆
example : (↑(0 : ℕ) : ℝ⋆) = zero := by
  -- show (Hyper.mk (↑0) 0 0) = zero
  show (Hyper.mk 0 0 0) = zero
  rw [Nat.cast_zero]
  rfl

example : (↑0 : ℝ⋆) = (O : ℝ⋆) := by
  have h : (Hyper.mk 0 0 0) = O := by
    rfl
  show (↑0 : ℝ⋆) = (Hyper.mk 0 0 0)
  exact h
  rfl -- doesn't work


example : (↑(0:ℕ) : ℝ⋆) = (zero : ℝ⋆) := by
  show (↑(0:ℝ) : ℝ⋆) = (↑(0:ℝ) : ℝ⋆) -- zero
  -- show (Hyper.mk 0 0 0) = O
  rfl -- doesn't work


example : (↑0 : ℝ*) = (zero : ℝ*) := by
  rfl

-- Another example using a natural number
example : (↑1 : ℝ*) = (one : ℝ*) := by
  rfl

-- defines:
-- def mul (a b : Hyper) : Hyper :=
--   Hyper.mk (a.real_part * b.real_part + a.epsilon_part * b.infinite_part)
--             (a.real_part*b.epsilon_part +a.epsilon_part*b.real_part) -- + a.epsilon_part * b.epsilon_part => ε^2 / 0 ?
--             (a.real_part*b.infinite_part + a.infinite_part*b.real_part ) -- a.infinite_part * b.infinite_part => ω^2 !

--  VIA COERCION :
-- def mul_hyper_real (a : Hyper) (b : Real) : Hyper :=
--   Hyper.mk (a.real_part * b)
--             (a.epsilon_part * b)
--             (a.infinite_part * b)

-- def mul_real_hyper (a : Real) (b : Hyper) : Hyper :=
--   Hyper.mk (a * b.real_part)
--             (a * b.epsilon_part)
--             (a * b.infinite_part)

example : ofReal 0 = zero := by
  rfl

-- example : (0:ℝ) = zeroh := by
example : (↑0 : ℝ*) = (zero: ℝ*) := by
  rfl

-- failed to synthesize instance
--   OfNat ℝ* 0


example : zero == 0 := by
  -- show (0 : ℝ⋆) = zero
  -- show (0 : ℝ⋆) = ⟨0, 0, 0⟩
  show (0 : ℝ⋆) = zero
  rfl

example : 1 = one := rfl


-- axiom epsilon_mul_omega_gauging : ε * ω = one
axiom epsilon_mul_omega_gauging : mul ε ω = one
-- axiom epsilon_mul_omega_gauging : ∀ (x : ℝ) , ( x ≠ 0 ) → (ε * ω = 1)
-- axiom epsilon_mul_omega_gauging : ∀ (ε ω : ℝ), (ε ≠ 0) → (ω ≠ 0) → (ε * ω = 1)


-- Define the standard part function
def standardPart (x : Hyper) : EReal :=
  if x.infinite_part==0 then x.real_part else if x.infinite_part > 0 then ∞ else -∞

-- lemmas about ε and ω
-- lemma ε_times_ω_equals_one : ε * ω = 1 := by
--   rw [Mul, ε, ω]
--   -- further simplifications and algebraic manipulation needed
--   sorry -- placeholder for proof


def main : IO UInt32 := do
  IO.println "Hello, tree!"
  pure 0

#eval main




-- Declare hyperreals as an extension of the reals
-- constant hyperreal : Type
-- constant ℝ* : Type
-- notation `ℝ*` := hyperreal
-- notation `ℝ*` := ℝ*

-- -- Declare infinitesimal and infinite numbers
-- constant epsilon : ℝ*
-- constant omega : ℝ*

-- -- Axioms for epsilon and omega
-- axiom epsilon_infinitesimal : ∀ r : ℝ, r > 0 → epsilon < r
-- axiom omega_infinite : ∀ r : ℝ, omega > r
-- axiom epsilon_omega_relation : epsilon * omega = 1

-- -- Additional axioms for ℝ*
-- -- Closure under ℝ operations
-- axiom add_closure : ∀ x y : ℝ*, x + y ∈ ℝ*
-- axiom mul_closure : ∀ x y : ℝ*, x * y ∈ ℝ*


-- -- transfer principle for hyperreals
-- axiom transfer : ∀ {P : ℝ → Prop}, (∀ r : ℝ, P r) → P epsilon → P omega → ∀ r : ℝ*, P r

-- Define the standard part function
def standardPart (x : ℝ*) : ℝ := -- ℝ∞
  if x > 0 then 1 else if x < 0 then -1 else 0

end Hypers
end Hypers
