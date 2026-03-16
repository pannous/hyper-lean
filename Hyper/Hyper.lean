-- TODO: Use currently best implementation: HyperGenerals
-- Things that should hold regardless of implementation :
import Hyper.HyperGeneral

-- TODO Write everything that should be true as a theorem, even if it's backed by sorry or axioms 

#eval  ω * ε == 1-- [(1, 0)] OK
#eval  2ε *ω  == 2 -- [(2, 0)] OK

-- 1 + 2ω + 1 + 2ω  ≈ ([1,0],[2,1],[1,0],[2,1]]) => ([2,0],[4,1)) ≈ 2 + 4ω
def simplify (a:R*) : R* :=
  ⟨a.components.foldl (λ acc x => acc ++ [x]) []⟩

#eval simplify (1:𝔽*) + ω + 1 + 1/ε -- 2 + 4ω
-- #eval simplify (1:𝔽*) + 2*ω + 1 + 2*ω -- 2 + 4ω