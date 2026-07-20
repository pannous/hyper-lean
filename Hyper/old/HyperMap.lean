-- import Std.Data.RBMap
import Lean.Data.RBMap
-- import Std.Data.HashMap BAD, no merging
import Mathlib.Data.Real.Basic -- for ℚ and ℤ wtf


namespace Hypers
section HyperMap

-- open Lean

notation "𝔽" => ℚ -- our field (for now), true alias

-- Representing hyper real numbers as coefficient to exponents:
-- e.g. (3ω⁻¹ + 1 + 3ω²) = {(-1, 3), (0, 1), (2, 3)}
def HyperMap := Lean.RBMap ℤ 𝔽 compare  -- terms for exponents
-- def HyperMap : Type := RBMap ℝ ℝ compare  -- generalized coefficient and exponents e.g. 3√ω + π


instance : Zero HyperMap where
  zero := Lean.RBMap.empty

instance : One HyperMap where
  one := Lean.RBMap.ofList [(0, 1)]

instance : OfNat HyperMap 0 where
  ofNat := Zero.zero

instance : OfNat HyperMap 1 where
  ofNat := One.one

instance : OfNat HyperMap n where
  ofNat := Lean.RBMap.ofList [(0, n)]


-- Adding an instance for addition in HyperMap
instance : Add HyperMap where
  add f g := f.fold (fun acc k v => acc.insert k (v + g.findD k 0)) g
