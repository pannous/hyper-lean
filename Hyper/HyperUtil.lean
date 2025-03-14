import Mathlib.Data.Real.Basic -- Import basic real number theory in LEAN 4
-- import Mathlib.Data.Real.Ereal -- ∞

-- ⚠️⚠️⚠️ Including this file messed up your original file be careful ⚠️⚠️⚠️

open Lean Meta

def saveTheorems  : MetaM Unit := do -- ⚠️ takes a while to run!!
  let env ← getEnv
  let found_count ← IO.mkRef 0
  -- let outFile ← IO.mkRef (← IO.FS.Handle.mk "lean_theorems.txt" IO.FS.Mode.write)
  let mut outFile ← IO.FS.Handle.mk "search_results.txt" IO.FS.Mode.write
  outFile.putStrLn s!"Theorem▸Type"
  for (name, decl) in env.constants.toList do
      let declName := name.toString
      let declType ← Meta.ppExpr decl.type
      found_count.modify (· + 1)
      outFile.putStrLn s!"Theorem: {declName}\nType: {declType}\n"
  outFile.flush
  let count ← found_count.get
  IO.println s!"Search complete. Found {count} theorems. Results saved to lean_theorems.txt"

-- where
  -- isTheorem (name: Name) : MetaM Bool := do
  --   let some const ← getConstInfo? name | return false
  --   pure $ const.isTheorem

-- #eval saveTheorems  -- ⚠️ takes a while to run!!
-- mouse over → busily processing

-- String.contains checks if a string contains a Char !!! no other method WTH !?
def contains (s sub : String) : Bool :=
  let sLen := s.length
  let subLen := sub.length
  if subLen = 0 then true
  else if subLen > sLen then false
  else
    -- Check all possible starting positions
    (List.range (sLen - subLen + 1)).any (fun i =>
      s.substrEq ⟨i⟩ sub ⟨0⟩ subLen)

-- #eval contains "hello world" "world"  -- true
-- #eval contains "Lean" "Haskell"       -- false

def searchTheorems (query: String) : MetaM Unit := do
  let env ← getEnv
  let found_count ← IO.mkRef 0
  env.constants.forM fun name _ => do
    if contains name.toString query then
      println! "{name}"
      found_count.modify (· + 1)

  let foundCount ← found_count.get
  println! "Total found: {foundCount}"

-- #eval searchTheorems "negative_smaller_zero"  -- ⚠️ takes a while to run!!
-- mouse over → busily processing
-- #eval searchTheorems "lt_zero"  -- ⚠️⚠️⚠️⚠️⚠️ takes a while to run!! ⚠️⚠️⚠️⚠️⚠️⚠️

variable {T : Type} [DecidableEq T] [LT T] [DecidableRel (LT.lt : T → T → Prop)]
variable {S : Type} [DecidableEq S] [LT S] [DecidableRel (LT.lt : S → S → Prop)]

-- Define the less-than relation for pairs (lexicographic order)
instance : LT (T × S) where
  lt := λ a b => a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)

instance genericPairsDecidableRel: DecidableRel (LT.lt : T × S → T × S → Prop) :=
  fun (a,b) (c,d) =>
    if h₁ : a < c then isTrue (Or.inl h₁)
    else if h₂ : a = c then
      if h₃ : b < d then
        isTrue (Or.inr ⟨h₂, h₃⟩)
      -- the rest is even more silly since we have to turn everything around
      else isFalse (λ (h : a < c ∨ (a = c ∧ b < d)) =>
        Or.elim h
        (λ hlt : a < c => absurd hlt h₁)
        (λ heq : a = c ∧ b < d =>
        absurd (And.right heq) h₃))
    else isFalse (λ (h : a < c ∨ (a = c ∧ b < d)) =>
        Or.elim h
        (λ hlt : a < c => absurd hlt h₁)
        (λ heq : a = c ∧ b < d =>
          absurd (And.left heq) h₂)
          )

-- def coerce_pair (p : ℕ × ℕ) : ℤ × ℤ := (p.1, p.2)

-- example : Decidable ((3, 4) < (3, 5) : ℤ × ℤ → ℤ × ℤ → Prop) := genericPairsDecidableRel -- Should succeed
-- example : (3, 4) < (3, 5)  := by exact genericPairsDecidableRel -- Should succeed

-- instance : DecidableRel (LT.lt : ℕ × ℕ → ℕ × ℕ → Prop) := genericPairsDecidableRel
-- ⅟ ½ ⅓ ⅔ ¼ ¾ ⅕ ⅖ ⅗ ⅘ ⅙ ⅚ ⅐ ⅛ ⅜ ⅝ ⅞
-- notation "⅟" x := (1 / x)
-- def half: ℚ := 1 / 2
-- notation "½" => half
prefix:10 "⅟" => fun x => 1 / x
-- #eval ⅟2.

-- ⁻¹ ⁰ ¹ ² ³ ⁴ ⁵ ⁶ ⁷ ⁸ ⁹

notation "½" => (1 / 2 : ℚ)
notation "⅓" => (1 / 3 : ℚ)
notation "⅔" => (2 / 3 : ℚ)
notation "¼" => (1 / 4 : ℚ)
notation "¾" => (3 / 4 : ℚ)
notation "⅕" => (1 / 5 : ℚ)
notation "⅖" => (2 / 5 : ℚ)
notation "⅗" => (3 / 5 : ℚ)
notation "⅘" => (4 / 5 : ℚ)
notation "⅙" => (1 / 6 : ℚ)
notation "⅚" => (5 / 6 : ℚ)
notation "⅐" => (1 / 7 : ℚ)
notation "⅛" => (1 / 8 : ℚ)
notation "⅜" => (3 / 8 : ℚ)
notation "⅝" => (5 / 8 : ℚ)
notation "⅞" => (7 / 8 : ℚ)

-- #eval ½+⅕

-- #eval ½+½+½
-- #eval 2+½
-- #eval 2*½
-- #eval (-1, -2) < (2, 1)
-- #eval (½, 2) < (2, 1)
-- #eval (2, 2) < (2, 2)
-- #eval (2, 2) <= (2, 2)
-- #eval (2, 1) < (2, 1)
-- #eval (2, 1) > (2, 1)
-- #eval (2, 1) >= (2, 1)
-- #eval (2, 1) = (2, 1)

-- end Pair

set_option quotPrecheck false
-- we may import the ereal later
-- import Mathlib.Data.Real.Ereal
notation "∞" => (⊤ : EReal)
notation "-∞" => (⊥ : EReal)
set_option quotPrecheck true

notation "(" a ",∞)" => Set.Ioi a -- (a,∞) = {x: a<x}
notation "(-∞," a ")" => Set.Iio a -- (-∞,a) = {x: x<a}
notation "(-∞,∞)" => Set.Univ -- (-∞,∞) = ℝ OR WHATEVER THE DOMAIN IS!

def square {α : Type*} [Mul α] (x : α) : α := x * x
def inv_square {α : Type*} [Inv α] [Mul α]  (x : α) : α := (x * x)⁻¹

instance : Inv Float where
  inv := fun x => 1 / x

notation x "²" => square x
notation x "⁻²" => inv_square x


instance : ToString ℚ where
  toString q :=
    if q.den = 1 then
      toString q.num  -- Just show the numerator if the denominator is 1
    else
      toString q.num ++ "/" ++ toString q.den

instance : ToString Bool where
  toString ja :=
    if ja then "true" else "false"

-- notation "huh" => sorry
-- notation "doh" => sorry
macro "todo" : tactic => `(tactic| sorry) -- todo + text
macro "obvious" : tactic => `(tactic| sorry)
macro "excercise" : tactic => `(tactic| sorry)

-- notation "definition" => rfl
-- macro "definition" : tactic => `(tactic| rfl;simp)
-- macro "definition" : tactic => `(tactic| try rfl <|> try simp <|> try unfold Neg.neg; unfold OfNat.ofNat)
macro "definition" : tactic => `(tactic| rfl)
example : 1 + 1 = 2 := by definition

macro "rofl" : tactic => `(tactic| rfl)
macro "reflexivity" : tactic => `(tactic| rfl)
macro "expansion" : tactic => `(tactic| rfl) -- expand definitions
-- macro "reduction" : tactic => `(tactic| rfl) -- reduce to definition
-- macro "reducing" : tactic => `(tactic| rfl) -- reduce to definition
-- macro "reduce" : tactic => `(tactic| rfl) -- reduce to definition

open Lean Elab Command

syntax "proposition" ident (ppSpace (colGt ident <|> term))* ":" term ":=" term : command
macro_rules | `(proposition $name:ident $args* : $type := $proof) => `(lemma $name $args* : $type := $proof)

proposition testProp : 1 + 1 = 2 := by rfl

syntax "fact" ident (ppSpace (colGt ident <|> term))* ":" term ":=" term : command
macro_rules | `(fact $name:ident $args* : $type := $proof) => `(lemma $name $args* : $type := $proof)

fact testFact : 1 + 1 = 2 := by rfl


syntax "corollary" ident (ppSpace (colGt ident <|> term))* ":" term ":=" term : command
macro_rules | `(corollary $name:ident $args* : $type := $proof) => `(lemma $name $args* : $type := $proof)

corollary testCorollary : 1 + 1 = 2 := by rfl

-- cast Nat to Prop / Bool
instance : OfNat Prop 0 where ofNat := false
instance : OfNat Prop 1 where ofNat := true
instance : OfNat Bool 0 where ofNat := false
instance : OfNat Bool 1 where ofNat := true
instance : Coe ℤ Bool where coe r := r ≠ 0
instance : Coe ℤ Prop where coe r := r ≠ 0

-- -- Replace the axiom with a computable implementation
-- /-- Approximates a real number as a rational with specified precision -/
-- def toRationalApprox (r : ℝ) (precision : Nat := 1000000) : ℚ :=
--   -- Use ToRat typeclass from Lean's standard library to convert a real to a rational
--   -- This is a computable operation with bounded precision
--   let n := (r * precision).toInteger
--   ⟨n, precision⟩

-- -- Use the computable version instead of the axiom
-- -- axiom closest_ratio : ℝ → ℚ -- arbitrary rational approximation (not computable)

-- instance : Coe ℝ ℚ⋆ where
--   coe r := Hyper.mk (toRationalApprox r) 0 0 0

-- def hyper : ℝ → Hyper := λ r => ⟨(toRationalApprox r), 0, 0, 0⟩

-- -- Optionally, allow specifying precision for more accurate approximations
-- def hyperWithPrecision (r : ℝ) (precision : Nat := 1000000) : Hyper :=
--   ⟨(toRationalApprox r precision), 0, 0, 0⟩



syntax "#assert" term : command

-- unsafe def fatalAssert (cond : Bool) (msg : String) : Unit := if ¬cond then (unsafeCast (panic! msg) : Unit) else ()
-- macro_rules | `(#assert! $cond) => `(#eval! fatalAssert $cond s!"Assertion failed: $($cond)")
-- macro_rules | `(#assert $cond) => `(if $cond then () else throw (IO.userError s!"Assertion failed: $($cond)"))
-- macro_rules | `(#assert $cond) => `(if $cond then #eval Except.ok () else #eval Except.error s!"Assertion failed: $(quote $(Lean.toExpr cond))")
-- macro_rules | `(#assert $cond) => `( #eval if $cond then () else panic! s!"Assertion failed: $($cond)")
-- macro_rules | `(#assert $cond) => `(#eval if $cond then Except.ok () else Except.error s!"Assertion failed: $(quote $cond)")
-- macro_rules | `(#assert $cond) => `(#eval if $cond then Except.ok () else Except.error s!"Assertion failed: {quote $cond}")
macro_rules | `(#assert $cond) => `(#eval if $cond then Except.ok () else Except.error s!"Assertion failed!")
-- macro_rules | `(#assert $cond) => `(#eval if $cond then Except.ok () else Except.error s!"Assertion failed: $(quote $(Lean.toExpr cond))")


-- Example Usage
-- #assert (1 + 1 = 2)  -- Does nothing
-- #assert (1 + 1 = 3)
-- #assert (1 + 1 = 3) "Math is broken!"  -- Panics with "Math is broken!"
