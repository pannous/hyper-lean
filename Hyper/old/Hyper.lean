-- TODO: Use currently best implementation: HyperGenerals
-- Things that should hold regardless of implementation :
import Hyper.old.HyperGeneral

-- TODO Write everything that should be true as a theorem, even if it's backed by sorry or axioms 

#eval  ω * ε == 1-- [(1, 0)] OK
#eval  2ε *ω  == 2 -- [(2, 0)] OK

#eval simplify (1:𝔽*) + ω + 1 + 1/ε -- 2 + 4ω
-- #eval simplify (1:𝔽*) + 2*ω + 1 + 2*ω -- 2 + 4ω