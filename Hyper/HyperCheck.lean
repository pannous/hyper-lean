import Hyper.HyperSort
-- import HyperSort
#eval ([]:𝔽*) = (0:𝔽*)
#eval ([]:𝔽*) = []
#eval (0:𝔽*) = []
#eval (0:𝔽*)
#eval (1:𝔽*)
#eval one + one
#eval 0 + one
#eval 1 + one
#eval -1 + one
#eval 1 - one
#eval -1 - one
#eval one + zero
#eval one + 0
#eval one + 1
#eval one - 1
#eval one + (1:R*)
#eval one + (1,0)
#eval one + [(1,0)]
#eval one + ((1,0):R*)
#eval (1,0) + one
#eval [((1:ℕ),(0:ℕ))] + one
#eval [((1:𝔽),(0:𝔽))] + one
#eval ((1,0):R*) + one
#eval ([(1,0)]:R*) + one
#eval ([⟨1,0⟩] : R*)
#eval ([(1,0)] : R*)
#eval ((1,0) : R*) + (1,0)
#eval ⟨1,0⟩ + (1,0)
#eval (1,0) + (1,0)
#eval [(1,0)]  + (1,0)
#eval ([] : R*) ++ [(1,0)]
#eval ([(1,0)] : R*) ++ [(1,0)]
#eval [(1,0)] ++ []
#eval [(1,0)] ++ ([] : R*)
#eval [(1,0)] ++ ([(1,0)] : R*)
#eval [(1,0)] ++ ((1,0) : R*) -- FAILS unless
#eval  ω * ε
#eval  2*ω * ε
#eval ε
#eval 1/ε - ω
#eval ω - ω
#eval ω - ω = O
#eval ω - ω = 0
#eval  2ω * ε
#eval  1 + 2ω + 1 + 2ω
