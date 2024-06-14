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


-- unfold Mul.mul instead of Hyper.mul NEVER HELPS :(
-- unfold Mul.mul at product  -- Explicitly unfold multiplication at 'product'  e.g. let product := (0 : Hyper) * (a:Hyper)
instance : Mul Hyper where
  mul x y :=
    ⟨ x.real_part * y.real_part + x.epsilon_part * y.infinite_part + x.infinite_part * y.epsilon_part,
      x.real_part * y.epsilon_part + x.epsilon_part * y.real_part,
      x.real_part * y.infinite_part + x.infinite_part * y.real_part ⟩


-- Explicitly stating HMul might help if Lean does not infer it automatically
instance : HMul Hyper Hyper Hyper where
  hMul := Mul.mul

--  HSMul.hSMul
instance : HSMul ℤ Hyper Hyper where
  hSMul z a := ⟨(z:ℝ) * a.real_part, (z:ℝ) * a.epsilon_part, (z:ℝ) * a.infinite_part⟩

instance : HSMul ℝ Hyper Hyper where
  hSMul r a := ⟨r * a.real_part, r * a.epsilon_part, r * a.infinite_part⟩

instance : HSMul ℕ Hyper Hyper where
  hSMul z a := ⟨(z:ℝ) * a.real_part, (z:ℝ) * a.epsilon_part, (z:ℝ) * a.infinite_part⟩

instance : HSMul ℚ Hyper Hyper where
  hSMul z a := ⟨(z:ℝ) * a.real_part, (z:ℝ) * a.epsilon_part, (z:ℝ) * a.infinite_part⟩

instance : HSMul ℚ≥0 Hyper Hyper where
  hSMul z a := ⟨(z:ℝ) * a.real_part, (z:ℝ) * a.epsilon_part, (z:ℝ) * a.infinite_part⟩


-- Define the instance of OfNat for Hyper

-- instance : OfReal Hyper x where
--   ofNat := Hyper.mk (x : ℝ) 0 0

-- Boolean equality of hyperreals
noncomputable -- because it depends on 'Real.decidableEq', and it does not have executable code
instance : BEq Hyper :=
  ⟨fun x y => x.real_part == y.real_part && x.epsilon_part == y.epsilon_part && x.infinite_part == y.infinite_part⟩

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


def maxFloat : Float := 1.7976931348623157e+308

noncomputable -- why not??
instance : Inv Hyper where
  inv (x:Hyper) :=
    if x == 0 then 0 -- The inverse of 0 is 0 by convention. !?!?
    else if x.real_part ≠ 0 ∧ x.epsilon_part ≠ 0 ∧ x.infinite_part ≠ 0 then
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
  rfl


lemma hyper_coercion_0: (0:ℝ) = (0:ℝ⋆) := by
  rfl

lemma hyper_coercion_1: (1:ℝ) = (1:ℝ⋆) := by
  rfl


lemma hyper_coercion_nat0: 0 = (0:ℝ⋆) := by
  rfl

lemma hyper_coercion_nat: (0:ℕ) = (0:ℝ⋆) := by
  -- #check Coe (ℕ → ℝ) -- Checks if there is a coercion from ℕ to ℝ  -- OK via Sort types
  -- #check Coe (ℝ → ℝ⋆) -- Checks if there is a coercion from ℝ to ℝ⋆
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
--   let left := (0:ℝ) * (a : ℝ) + (0:ℝ) * (b : ℝ)
--   let right := (0:ℝ⋆)
--   rw [hyper_zero_is_zero]
--   have right_ok: right = 0 := by apply hyper_zero_is_zero
--   -- apply right_ok
--   -- show (0:ℝ) * (a : ℝ) + (0:ℝ) * (b : ℝ) = 0
--   -- rw [zero_times_anything]
--   -- ring
--   rw [right_ok]
  -- exact zero_times_anything

-- lemma zero_times_anything0part: (0:ℝ) * (a : ℝ) + (0:ℝ) * (b : ℝ) = Hyper.real_part 0 := by
  -- let right := Hyper.real_part 0
  -- have h : right = 0 := by
  --   rfl
  -- show right = 0
  -- {sorry}
  -- ring

-- lemma zero_times_anything0epart: (0:ℝ) * (a : ℝ) + (0:ℝ) * (b : ℝ) = Hyper.epsilon_part 0 := by
--   sorry

-- lemma hyper_zero_mul0 (a : Hyper) : 0 * a = 0 := by

lemma hyper_real_part_one_is_1: (1:Hyper).real_part = 1 := by
  rfl

lemma hyper_real_part_zero_is_0: (0:Hyper).real_part = 0 := by
  rfl

-- lemma hyper_real_part_zero_is_zero: Hyper.real_part (0:Hyper) = (0:ℝ) := by
--   rfl

-- lemma hyper_real_part_one_is_one: Hyper.real_part 1 = (1:ℝ) := by
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

lemma hyper_one_mul (a : Hyper) : 1 * a = a := by
  apply Hyper.ext
  { show 1 * a.real_part + 0 * a.infinite_part + 0 * a.epsilon_part = a.real_part; ring }
  { show 1 * a.epsilon_part + 0 * a.real_part = a.epsilon_part; ring }
  { show 1 * a.infinite_part + 0 * a.real_part = a.infinite_part; ring }


lemma hyper_mul_zero (a : Hyper) : a * 0 = 0 := by
  -- let mu := a * (0:Hyper)
  -- unfold Mul.mul at mu
  apply Hyper.ext
  { show a.real_part * 0 + a.epsilon_part * 0 + a.infinite_part *0 = 0; ring }
  { show a.real_part * 0 + a.epsilon_part * 0 = 0; ring }
  { show a.real_part * 0 + a.infinite_part * 0 = 0; ring }

lemma hyper_mul_one (a : Hyper) : a * 1 = a := by
  apply Hyper.ext
  { show a.real_part * 1 + a.epsilon_part * 0 + a.infinite_part *0 = a.real_part ; ring }
  { show a.real_part * 0 + a.epsilon_part * 1 = a.epsilon_part; ring }
  { show a.real_part * 0 + a.infinite_part * 1 = a.infinite_part; ring }

--  SAME ^^
-- lemma hyper_0_mul (a : Hyper) : (0:Hyper) * a = (0:Hyper) := by


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
lemma hyper_inv_cancel (a : Hyper) (h : a ≠ 0) : a * a⁻¹ = 1 := by
  sorry

theorem hyper_inv_zero : (0 : Hyper)⁻¹ = 0 :=
  sorry

-- lemma hyper_inv_zero (a : Hyper) (h : a = 0) : a⁻¹ = 0 := by
--   sorry

-- instance : Inv Hyper where
--   inv (x:Hyper) :=
--     if x == 0 then 0 -- The inverse of 0 is 0 by convention. !?!?

-- theorem hyper_inv_zero : (0 : Hyper)⁻¹ = 0 :=
--   let inv := (0 : Hyper)⁻¹;
--   -- Begin the proof block
--   show inv = 0 from
--   -- Evaluate the definition of inverse on zero
--   match (0 : Hyper), inv with
--   | _, inv =>
--     -- Assert and check the condition directly
--     if h : (0 : Hyper) = 0 then -- failed to synthesize instance Decidable (0 = 0)
--       -- Here we use the true branch of the if statement
--       by simp [Inv.inv, h]
--     else
--       -- Handle the false branch, which is theoretically unreachable
--       by contradiction


-- The inverse of 0 is 0 by convention. !?!?
-- lemma hyper_inv_zero : (0:Hyper)⁻¹ = 0 := by
--   let inv := (0:Hyper)⁻¹
--   unfold Inv.inv at inv
--   have inv_0: inv = (0:Hyper) := by sorry
--   exact inv_0
  -- use definition of inverse for proof



lemma hyper_mul_comm (a b : Hyper) : a * b = b * a := by
  apply Hyper.ext
  { show a.real_part * b.real_part + a.epsilon_part * b.infinite_part + a.infinite_part * b.epsilon_part = b.real_part * a.real_part + b.epsilon_part * a.infinite_part + b.infinite_part * a.epsilon_part; ring }
  { show a.real_part * b.epsilon_part + a.epsilon_part * b.real_part = b.real_part * a.epsilon_part + b.epsilon_part * a.real_part; ring }
  { show a.real_part * b.infinite_part + a.infinite_part * b.real_part = b.real_part * a.infinite_part + b.infinite_part * a.real_part; ring }
  -- UFF, OK! 😺


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
  let br := b.real_part
  let be := b.epsilon_part
  let bi := b.infinite_part
  let cr := c.real_part
  let ce := c.epsilon_part
  let ci := c.infinite_part

  -- unfold Add.add at right
  apply Hyper.ext
  -- { show ar * (br + cr) + ae * (bi + ci) + ai * (be + ce) = ar * br + ae * be + ai * bi + ar * cr + ae * ce + ai * ci; ring }
  { sorry }
  { sorry }
  { sorry }
  -- { show ar * (be + ce) + ae * (br + cr) = ar * be + ar * ce + ae * br + ae * cr; ring }
  -- { show ar * (be + ce) + ae * (br + cr) = ar * be + ae * br + ar * ce + ae * cr; ring }
  -- { show ar * (bi + ci) + ai * (br + cr) = ar * bi + ai * br + ar * ci + ai * cr; ring }



lemma hyper_mul_assoc (a b c : Hyper) : a * b * c = a * (b * c) := by
  let left := a * b * c
  let right := a * (b * c)
  unfold Mul.mul at left
  unfold Mul.mul at right
  -- have right_is: right = a.real_part * b.real_part * c.real_part + a.epsilon_part * b.infinite_part * c.infinite_part := by simp
  apply Hyper.ext
  {sorry}
  {sorry}
  {sorry}



lemma hyper_right_distrib (a b c : Hyper) : (a + b) * c = a * c + b * c := by
  apply Hyper.ext
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
  -- have : (0:ℝ) = (1:ℝ) := h1
  -- This is a clear contradiction as 0.0 ≠ 1.0
  exact absurd this (ne_of_lt (by norm_num)) -- (by decide)


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
  mul_inv_cancel:= hyper_inv_cancel,
  mul_comm:= hyper_mul_comm,
  inv_zero:=  hyper_inv_zero, -- (0:Hyper)⁻¹ = 0, The inverse of 0 is 0 by convention. !?!?
  left_distrib:= hyper_left_distrib,
  right_distrib:= hyper_right_distrib,
  zsmul:= HSMul.hSMul,
  nsmul:= HSMul.hSMul,
  qsmul:= HSMul.hSMul,
  nnqsmul:= HSMul.hSMul, -- (· • ·)
  exists_pair_ne:=⟨ 0 , 1 , zero_ne_one ⟩,
}
  /--
  -- The hyperreal numbers ℝ⋆ form a linear ordered field.
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







lemma product_zero_means_arg_is_zero (a b : Hyper) (h : a * b = 0) :  a = 0 ∨ b = 0 := by
  exact mul_eq_zero.mp h  -- USE EXISTING FIELD THEORY for our Hyper! 😺

end Hypers
end Hypers
