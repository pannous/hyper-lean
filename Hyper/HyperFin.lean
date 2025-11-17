import Mathlib.Data.Finset.Basic
-- import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic -- for ℚ and ℤ wtf

notation "𝔽" => ℚ  -- Field (for now)

def HyperMap := Finset (ℤ × 𝔽)

namespace HyperMap

instance : EmptyCollection HyperMap where
  emptyCollection := Finset.empty

-- Zero and One
instance : Zero HyperMap where
  zero := ∅

instance : One HyperMap where
  one := Finset.mk {(0, 1)} (by simp)

instance : OfNat HyperMap 0 where
  ofNat := Zero.zero

instance : OfNat HyperMap 1 where
  ofNat := One.one

instance : OfNat HyperMap n where
  ofNat := Finset.mk {(0, (n:𝔽))} (by simp)

notation "ø" => {}

noncomputable
def lookup (m : HyperMap) (e : ℤ) : 𝔽 :=
  match (m.filter (λ (e', _) => e' = e)).toList with
  | (⟨_, c⟩ :: _) => c
  | [] => 0

-- def lookup1 (m : HyperMap) (e : ℤ) : 𝔽 :=
--   match m.find? (λ (e', _) => e' = e) with
--   | some (_, c) => c
--   | none => 0


-- Custom merging function for union
def merge (f g : HyperMap) : HyperMap :=
  (f.val ++ g.val).eraseDups.map (λ (e, _) => (e, f.lookup e + g.lookup e)) |>.toFinset

instance : Union HyperMap where
  union := merge

instance : Add HyperMap where
  add := merge

instance : Union HyperMap where
  union f g :=
    (f ∪ g).val.map (λ (e, c) => (e, f.lookup e + g.lookup e))
      |>.toFinset

instance : Add HyperMap where
  add f g :=
    (f ∪ g).val.map (λ (e, c) => (e, f.lookup e + g.lookup e))
      |>.filter (λ (_, c) => c ≠ 0)
      |>.toFinset

instance : Add HyperMap where
  add f g :=
    (f ∪ g).image (λ (e, c) => (e, f.lookup e + g.lookup e))
      |>.filter (λ (_, c) => c ≠ 0)


theorem add_comm (a b : HyperMap) : a + b = b + a := by
  ext (e, c)
  simp [HyperMap.lookup]
  rw [add_comm]

end HyperMap
