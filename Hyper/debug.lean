import Mathlib.Data.Real.Ereal


namespace HowToDebug


-- set_option trace.compiler.result true
#eval 1 + 1 == 2

-- namespace Hypers

-- HOW TO GET PROOF STEPS from rfl?  show_term rfl !!!
-- 1)
set_option pp.all true
-- 2)
-- lemma neg_zero : -0 = (0:R*) := by show_term rfl -- << THIS IS THE WAY: GET PROOF STEPS!
-- lemma neg_zero : -0 = (0:R*) := by rfl
-- lemma neg_zero : -0 = (0:R*) := by simp NOPE
-- lemma neg_zero : -0 = (0:R*) := by simp? NOPE
-- lemma neg_zero : -0 = (0:R*) := by aesop? -- YES!
-- lemma neg_zero : -0 = (0:R*) := by exact Eq.refl (-0) -- SAYS NOTHING!?!? --- as suggested here:
-- lemma neg_zero : -0 = (0:R*) := by exact @Eq.refl.{1} Hypers.Hyper (@Neg.neg.{0} Hypers.Hyper Hypers.instNegHyper (@OfNat.ofNat.{0} Hypers.Hyper 0 Hypers.instOfNatHyperOfNatNat))
-- lemma neg_zero : -0 = (0:R*) := by exact @Eq.refl.{1} Hyper (@Neg.neg.{0} Hyper instNegHyper (@OfNat.ofNat.{0} Hyper 0 instOfNatHyperOfNatNat))
-- lemma neg_zero : -0 = (0:R*) := by exact @Eq.refl.{1} R* (@Neg.neg.{0} R* instNegHyper (@OfNat.ofNat.{0} R* 0 instOfNatHyperOfNatNat))
-- lemma neg_zero : -0 = (0:R*) := by exact Eq.refl (@Neg.neg R* instNegHyper 0)
-- lemma neg_zero : -0 = (0:R*) := by exact Eq.refl (@Neg.neg R* instNegHyper _)
-- lemma neg_zero : -0 = (0:R*) := by refine Eq.refl (@Neg.neg R* instNegHyper _)
-- lemma neg_zero : -0 = (0:R*) := by simp [Neg.neg, zero] --   rfl
-- now that we understand the proof steps, we can write the lemma simplemost:
-- @[simp]
lemma neg_zero : -0 = 0 := by rfl

-- #reduce (-0 = (0 : R*))
#print neg_zero -- uses Eq.refl (-0) OK GIVE VERBOSE SHIT TO GPT TO SIMPLIFY ;)
