import Hyper.HyperSort
-- import HyperSort

namespace Hypers
-- open Hypers.HyperList
lemma one_plus_one_eq_two : one + one = 2 := by rfl

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
#eval one + [(1,0)]
#eval one + ((1,0):R*)
#eval [((1:ℕ),(0:ℕ))] + one
#eval [((1:𝔽),(0:𝔽))] + one
#eval ((1,0):R*) + one
#eval ([(1,0)]:R*) + one
#eval ([⟨1,0⟩] : R*) == one
#eval ([⟨1,0⟩] : R*) == 1
#eval ([⟨1,0⟩] : R*) = one
#eval ([⟨1,0⟩] : R*) = 1
#eval simplify ([⟨1,0⟩] : R*)
#eval ([(1,0)] : R*)
#eval ⟨1,0⟩ + (1,0)
#eval (1,0) + (1,0)
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

-- ERROR: need signiture or coe!
#eval one + (1,0)
#eval (1,0) + one
#eval ((1,0) : R*) + (1,0)
#eval [(1,0)]  + (1,0)

-- instance : Decidable ((x:R*) ≈ (y:R*)) :=
--   match decEq (simplify x) (simplify y) with
--   | isTrue h  => isTrue (by sorry) -- rw  [h])
--   | isFalse h => isFalse h



#eval (simplify ([(0,0)] : R*)) = (simplify (0: R*)) -- true OK
#eval (simplify ([(0,0)] : R*)) = (simplify ([]: R*)) -- true OK
#eval simplify ([(0,0)] : R*) = [] -- true OK

-- #eval ↑(0,0) == 0 -- error
#eval ↑(0,0) == ↑0 -- true OK why lol?
#eval ↑[(0,0)] == (0: R*) -- true OK why lol?
#eval ↑(0,0) == (0: R*) -- error if coe missing
#eval ((0,0) : R*) == (0: R*) -- error if coe missing
#eval ([(0,0)] : R*) == (0: R*) -- true iff BEq (List (ℚ × ℚ)) is defined WHY??
#eval ([(0,0)] : R*) == 0 -- error if OfNat missing
#eval ([(0,0)] : R*) == ↑0 -- error if OfNat missing

-- #eval ↑(0,0) == ↑[] -- error
#eval ↑[(0,0)] == ([]: R*) -- true OK why lol?
-- #eval ↑(0,0) == ([]: R*) -- error
#eval ((0,0) : R*) == ([]: R*) -- error if coe missing
#eval ([(0,0)] : R*) == ([]: R*) -- true iff BEq (List (ℚ × ℚ)) is defined WHY??
#eval ([(0,0)] : R*) == [] -- error if OfNat missing

-- #eval [] == ↑0 -- error
#eval [] == (0: R*) -- true OK
#eval ↑[] == (0: R*) -- true
#eval ([] : R*) == (0: R*) -- error if coe missing
#eval ([] : R*) == (0: R*) -- true iff BEq (List (ℚ × ℚ)) is defined WHY??
#eval ([] : R*) == 0 -- error if OfNat missing
#eval ([] : R*) == ↑0 -- error if OfNat missing


-- Since all of these can be rfl'ed they can be omitted (?)
lemma norm_zero_norm : ([(0,0)] : R*) == (0: R*) := by rfl
lemma norm_zero_pair : ↑(0,0) == (0: R*) := by rfl
lemma norm_zero_pair_nat : (↑(0,0) == ↑0) := by rfl
lemma norm_zero_list_pair : (↑[(0,0)] == (0: R*)) := by rfl
lemma norm_zero_pair_coe : (↑(0,0) : R*) == (0: R*) := by rfl
lemma norm_zero_typed_pair_coe : (((0,0) : R*) == (0: R*)) := by rfl
lemma norm_zero_list_pair_beq : ([(0,0)] : R*) == (0: R*)  := by rfl
lemma norm_zero_list_pair_ofnat :  (([(0,0)] : R*) == 0) := by rfl
lemma norm_zero_list_pair_ofnat_nat :  (([(0,0)] : R*) == ↑0) := by rfl

-- lemma norm_zero_pair_empty :  (↑(0,0) == ↑[]) := by rfl
lemma norm_zero_list_pair_empty : (↑[(0,0)] == ([]: R*)) := by rfl
lemma norm_zero_typed_pair_empty :  (((0,0) : R*) == ([]: R*)) := by rfl
lemma norm_zero_list_pair_empty_beq : ([(0,0)] : R*) == ([]: R*) := by rfl
lemma norm_zero_list_pair_empty_ofnat :  (([(0,0)] : R*) == []) := by rfl

-- lemma norm_zero_empty_nat :  ([] == ↑0) := by rfl
lemma norm_zero_empty : ([] == (0: R*)) := by rfl
lemma norm_zero_coe_empty : (↑[] == (0: R*)) := by rfl
lemma norm_zero_typed_empty :  (([] : R*) == (0: R*)) := by rfl
lemma norm_zero_typed_empty_beq : ([] : R*) == (0: R*) := by rfl
lemma norm_zero_typed_empty_ofnat :  (([] : R*) == 0) := by rfl
lemma norm_zero_typed_empty_ofnat_nat :  (([] : R*) == ↑0) := by rfl


#eval BEq.beq [(0,0)] O  -- true iff BEq (List (ℚ × ℚ)) is defined because O = 0:R*
#eval BEq.beq [(0,0)] []  -- true iff BEq (List (ℕ × ℕ)) is defined
#eval BEq.beq ([(0,0)]:R*) [] -- true iff BEq (List (ℚ × ℚ)) is defined WHY??


lemma one_plus_zero_eq_one : one + zero = 1 := by rfl
lemma empty_eq_zero : ([] : 𝔽*) = (0 : 𝔽*) := by rfl
lemma empty_eq_empty : ([] : 𝔽*) = [] := by rfl
lemma zero_eq_empty : (0 : 𝔽*) = [] := by rfl
lemma eval_zero : (0 : 𝔽*) = 0 := by rfl
lemma eval_one : (1 : 𝔽*) = 1 := by rfl
lemma zero_plus_one : 0 + one = one := by rfl
lemma one_plus_zero : one + zero = one := by rfl
lemma one_plus_nat_zero : one + 0 = one := by rfl


-- TODO:
#eval one + one == 2 -- ok
-- lemma one_plus_one : one + one = 2 := by norm_num?
lemma one_plus_one : one + one == 2 := by decide
lemma one_plus_one : one + one = 2 := by decide
lemma one_plus_nat_one : 1 + one = 2 := by rfl
lemma neg_one_plus_one : -1 + one = 0 := by rfl
lemma one_minus_one : 1 - one = 0 := by rfl
lemma neg_one_minus_one : -1 - one = -2 := by rfl
lemma one_plus_nat_one_alt : one + 1 = 2 := by rfl
lemma one_minus_nat_one : one - 1 = 0 := by rfl
lemma one_plus_real_one : one + (1 : R*) = 2 := by rfl
lemma one_plus_tuple : one + (1,0) = 2 := by rfl
lemma one_plus_list_tuple : one + [(1,0)] = 2 := by rfl
lemma one_plus_tuple_real : one + ((1,0) : R*) = 2 := by rfl
lemma tuple_plus_one : (1,0) + one = 2 := by rfl
lemma list_tuple_plus_one : [((1 : ℕ), (0 : ℕ))] + one = 2 := by rfl
lemma list_tuple_f_plus_one : [((1 : 𝔽), (0 : 𝔽))] + one = 2 := by rfl
lemma tuple_real_plus_one : ((1,0) : R*) + one = 2 := by rfl
lemma list_tuple_real_plus_one : ([(1,0)] : R*) + one = 2 := by rfl
lemma list_tuple_real : ([⟨1,0⟩] : R*) = [(1,0)] := by rfl
lemma list_tuple_real_alt : ([(1,0)] : R*) = [(1,0)] := by rfl
lemma tuple_real_plus_tuple : ((1,0) : R*) + (1,0) = 2 := by rfl
lemma angle_bracket_tuple_plus_tuple : ⟨1,0⟩ + (1,0) = 2 := by rfl
lemma tuple_plus_tuple : (1,0) + (1,0) = 2 := by rfl
lemma list_tuple_plus_tuple : [(1,0)] + (1,0) = 2 := by rfl
lemma empty_list_concat : ([] : R*) ++ [(1,0)] = [(1,0)] := by rfl
lemma list_tuple_concat : ([(1,0)] : R*) ++ [(1,0)] = [(1,0), (1,0)] := by rfl
lemma list_tuple_concat_empty : [(1,0)] ++ [] = [(1,0)] := by rfl
lemma list_tuple_concat_empty_real : [(1,0)] ++ ([] : R*) = [(1,0)] := by rfl
lemma list_tuple_concat_real : [(1,0)] ++ ([(1,0)] : R*) = [(1,0), (1,0)] := by rfl

-- Special handling required for failure case:
lemma list_tuple_concat_tuple_real (h : (1,0) : R* ≠ [(1,0)]) : [(1,0)] ++ ((1,0) : R*) = [(1,0), (1,0)] := by rfl

lemma omega_times_epsilon : ω * ε = O := by rfl
lemma two_omega_times_epsilon : 2 * ω * ε = O := by rfl
lemma eval_epsilon : ε = ε := by rfl
lemma one_div_epsilon_minus_omega : 1 / ε - ω = O := by rfl
lemma omega_minus_omega : ω - ω = O := by rfl
lemma omega_minus_omega_eq_O : (ω - ω) = O := by rfl
lemma omega_minus_omega_eq_zero : (ω - ω) = 0 := by rfl
lemma two_omega_times_epsilon_alt : 2 * ω * ε = O := by rfl
lemma complex_sum : 1 + 2 * ω + 1 + 2 * ω = 2 + 4 * ω := by rfl

lemma one_plus_one_eq_two : one + one = 2 := by simp [one, one, merge, merge_nil_right, Add.add, merge_nil_left]
lemma one_plus_one_eq_two' : one + one = [(2,0)] := by rfl
