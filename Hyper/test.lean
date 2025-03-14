import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

-- Complex.ext_iff : ∀ {z w : ℂ}, z = w ↔ (z.re = w.re ∧ z.im = w.im)

-- for pairs:
-- instance : BEq (Nat × Nat) where
  -- beq (a1,b1) (a2,b2) := (a1 == a2) && (b1 == b2)

-- for lists:
instance [BEq α] : BEq (List α) where
  beq as bs :=
    match as, bs with
    | [],      []      => true
    -- | [],      (0,0)::[]      => true
    | a :: as, b :: bs => (a == b) && (as == bs)
    | _,       _       => false

#eval [1, 2, 3] == [1, 2, 3] -- true
#eval [1, 2, 3] == [1, 2, 4] -- false

open Complex Set

def real_as_complex : Type := {z : ℂ // z.im = 0}
def real_set : Set ℂ := {z : ℂ | z.im = 0}


def real_to_complex_embedding : ℝ →+* ℂ := -- ring homomorphism
  {
    toFun := Coe.coe,
    -- toFun := real_to_complex,
    -- toFun := λ r => Complex.mk r 0
    -- toFun := λ r => ⟨r, 0⟩, -- no proof needed?
    -- toFun := λ r => ⟨r, 0, rfl⟩,
    map_zero' := rfl,
    map_one' := rfl,
    -- map_add' := -- by
  --   intros x y
  --   dsimp [real_to_complex_embedding]
  --   simp [Complex.add_re, Complex.add_im]
    map_add' := by
      intros x y
      have h0 : (({ re := x, im := 0 }: ℂ) + { re := y, im := 0 }).re = (x + y) := by rw [Complex.add_re]
      have h1 : (({ re := x, im := 0 }: ℂ) + { re := y, im := 0 }).im = 0 := by rw [Complex.add_im, add_zero]
      exact Complex.ext_iff.2 ⟨Eq.symm h0, Eq.symm h1⟩
--     map_add'' := by
--       intros x y
--       simp [Complex.add_re, Complex.add_im]
--       let a : ℂ := { re := x, im := 0 }
--       let b : ℂ := { re := y, im := 0 }
--       let c : ℂ := { re := x + y, im := 0 }
--       let d : ℝ := x + y
-- -- theorem add_re (z w : ℂ) : (z + w).re = z.re + w.re := rfl
-- -- theorem add_im (z w : ℂ) : (z + w).im = z.im + w.im := rfl
--       show c = a + b
--       have h0 : (a + b).re = c.re := by rw [Complex.add_re];
--       have ha : (a + b).im = 0 + 0 := by rw [Complex.add_im];
--       have hax : (a + b).im = a.im + b.im := by rw [Complex.add_im];
--       have hc : (0:ℝ) + (0:ℝ) = (0:ℝ) := by simp; -- how to inline this? -- by rw [add_zero];
--       have hb : (a + b).im = 0 := by rw [Complex.add_im, add_zero];
--       have h1 : (a + b).im = c.im := by exact Eq.trans ha hb
--       have h0' : c.re = (a + b).re := by exact Eq.symm h0
--       have h1' : c.im = (a + b).im := by exact Eq.symm h1
--       have hc : c = a + b := by exact Complex.ext_iff.2 ⟨h0', h1'⟩
--       exact hc
    map_mul' := by
      intros x y
      -- show ((⟨x, 0⟩: ℂ) * ⟨y, 0⟩) = ⟨x * y, 0⟩
      have h0 : (({ re := x, im := 0 }: ℂ) * { re := y, im := 0 }).re = x * y :=
        by rw [Complex.mul_re, zero_mul, sub_zero] -- (x * y) - 0*0
      have h1 : (({ re := x, im := 0 }: ℂ) * { re := y, im := 0 }).im = 0 :=
        by rw [Complex.mul_im, mul_zero, zero_mul, add_zero] -- x*0 + 0*y
      exact Complex.ext_iff.2 ⟨Eq.symm h0, Eq.symm h1⟩
}

-- theorem real_to_complex_embedding_isomorphic_to_image :
  -- ∀ z : ℂ, z.im = 0 ↔ ∃ r : ℝ, real_to_complex_embedding r = z :=
-- proof details

example : (↑(ℝ) : Set ℂ) ⊂ univ :=
  ⟨fun x _ => trivial, fun h => by
    have : I ∈ (↑(ℝ) : Set ℂ) := by rw [h]; trivial
    simp [Complex.I_re, Complex.I_im] at this⟩

example : (ℝ : Set ℂ) ⊂ ℂ :=
  ⟨subset_univ _, fun h => by
    have : Complex.I ∈ ℝ := by rw [h]; trivial
    simp [Complex.I_re, Complex.I_im] at this⟩

example : (ℝ : Set ℂ) ⊂ ℂ := by
  simp [Set.ssubset_def, Set.subset_univ];
  exact Complex.ext_iff.2 (Or.inr ⟨0, by decide⟩)

example {a b : ℤ} : (a - b) * (a + b) = a^2 - b^2 := by
  calc
    (a - b) * (a + b) = a^2 - a*b + a*b - b^2 := by ring
    _ = a^2 - b^2 := by ring

def main : IO Unit :=
  IO.println "Hello, World!"

def addOne (n : Nat) : Nat := n + 1

theorem addOne_correct (n : Nat) : addOne n = n + 1 := by
  rfl

theorem add_zero (n : Nat) : n + 0 = n := by
  rfl

theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.add_succ]
    rw [ih]

-- set_option diagnostics true
-- def addOner (x : ℝ) : ℝ := x + (1 : ℝ)

-- theorem addOner_correct (x : ℝ) : addOner x = x + (1 : ℝ) := by
--   rfl

#eval main
#eval addOne 5  -- This will output 6
