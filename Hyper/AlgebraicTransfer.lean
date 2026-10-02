import Hyper.HyperAlgebraic

/-! Transfer principle for the root-closed algebraic hyperreals `HyperAlgebraic.Number`.

Keisler's Axiom E ("every real solution of S is a solution of T") is a
universal sentence `∀ x⃗, S x⃗ → T x⃗`. For quantifier-free formulas built
from `+ · - ⁻¹ √`, real constants, `=` and `<` this transfers from ℝ to
`Number` without ultrafilters or Tarski: an element is a germ `s ↦ x(s)` at
`s → ∞` with an eventually constant sign, so every formula is eventually true
or eventually false, and the hyperreal truth value is the eventual real one.

`√` as a function symbol is Keisler's Axiom D for the square root: the real
`√` extends to `Number`, so e.g. `∀ x ≥ 0, √x · √x = x` transfers. -/

noncomputable section
namespace AlgebraicTransfer
open Filter HyperAlgebraic

inductive Term (n : ℕ) where
  | var : Fin n → Term n
  | const : ℝ → Term n
  | add : Term n → Term n → Term n
  | mul : Term n → Term n → Term n
  | neg : Term n → Term n
  | inv : Term n → Term n
  | sqrt : Term n → Term n

/-- Evaluate in any field `F`, reading real constants through `embed`. -/
def Term.eval {n : ℕ} {F : Type*} [Field F] (embed : ℝ → F) (root : F → F) (v : Fin n → F) :
    Term n → F
  | var i => v i
  | const r => embed r
  | add a b => a.eval embed root v + b.eval embed root v
  | mul a b => a.eval embed root v * b.eval embed root v
  | neg a => -a.eval embed root v
  | inv a => (a.eval embed root v)⁻¹
  | sqrt a => root (a.eval embed root v)

inductive Formula (n : ℕ) where
  | eq : Term n → Term n → Formula n
  | lt : Term n → Term n → Formula n
  | not : Formula n → Formula n
  | and : Formula n → Formula n → Formula n
  | or : Formula n → Formula n → Formula n

def Formula.imp {n : ℕ} (a b : Formula n) : Formula n := .or (.not a) b

def Formula.Holds {n : ℕ} {F : Type*} [Field F] [LT F] (embed : ℝ → F) (root : F → F)
    (v : Fin n → F) : Formula n → Prop
  | eq a b => a.eval embed root v = b.eval embed root v
  | lt a b => a.eval embed root v < b.eval embed root v
  | not a => ¬a.Holds embed root v
  | and a b => a.Holds embed root v ∧ b.Holds embed root v
  | or a b => a.Holds embed root v ∨ b.Holds embed root v

/-- Truth in ℝ. -/
abbrev Formula.HoldsReal {n : ℕ} (φ : Formula n) (v : Fin n → ℝ) : Prop :=
  φ.Holds id Real.sqrt v

/-- Truth in the hyperreals. -/
abbrev Formula.HoldsHyper {n : ℕ} (φ : Formula n) (v : Fin n → Number) : Prop :=
  φ.Holds ofReal HyperAlgebraic.sqrt v

/-- The real tuple obtained by reading every hyperreal coordinate at `s`. -/
def realize {n : ℕ} (v : Fin n → Number) (s : ℝ) : Fin n → ℝ := fun i => rep (v i) s

/-- Evaluation commutes with reading at `s`, exactly (germs compute pointwise). -/
theorem Term.coe_eval {n : ℕ} (v : Fin n → Number) :
    ∀ t : Term n, ((t.eval ofReal HyperAlgebraic.sqrt v : Number) : Germs) =
      ↑(fun s => t.eval id Real.sqrt (realize v s))
  | var i => (coe_rep (v i)).symm
  | const r => coe_const r
  | add a b => by
    change (_ : Germs) + _ = _
    rw [a.coe_eval v, b.coe_eval v]; rfl
  | mul a b => by
    change (_ : Germs) * _ = _
    rw [a.coe_eval v, b.coe_eval v]; rfl
  | neg a => by
    change -(_ : Germs) = _
    rw [a.coe_eval v]; rfl
  | inv a => by
    change (_ : Germs)⁻¹ = _
    rw [a.coe_eval v]; rfl
  | sqrt a => by
    change Germ.map Real.sqrt (_ : Germs) = _
    rw [a.coe_eval v, Germ.map_coe]; rfl

theorem eq_decided {x y : Number} {f g : ℝ → ℝ} (hf : (f : Germs) = x) (hg : (g : Germs) = y) :
    (x = y → ∀ᶠ s in atTop, f s = g s) ∧ (x ≠ y → ∀ᶠ s in atTop, f s ≠ g s) :=
  ⟨fun h => Germ.coe_eq.mp (hf.trans (by rw [h, hg])), fun h => eventually_ne_of_ne h hf hg⟩

theorem lt_decided {x y : Number} {f g : ℝ → ℝ} (hf : (f : Germs) = x) (hg : (g : Germs) = y) :
    (x < y → ∀ᶠ s in atTop, f s < g s) ∧ (¬x < y → ∀ᶠ s in atTop, ¬f s < g s) :=
  ⟨(lt_iff_eventually hf hg).mp, fun h =>
    ((le_iff_eventually hg hf).mp (not_lt.mp h)).mono fun _ hs => not_lt.mpr hs⟩

theorem Formula.eventually_decided {n : ℕ} (v : Fin n → Number) :
    ∀ φ : Formula n, (φ.HoldsHyper v → ∀ᶠ s in atTop, φ.HoldsReal (realize v s)) ∧
      (¬φ.HoldsHyper v → ∀ᶠ s in atTop, ¬φ.HoldsReal (realize v s))
  | eq a b => eq_decided (a.coe_eval v).symm (b.coe_eval v).symm
  | lt a b => lt_decided (a.coe_eval v).symm (b.coe_eval v).symm
  | not a => by
    obtain ⟨hpos, hneg⟩ := a.eventually_decided v
    exact ⟨hneg, fun h => (hpos (not_not.mp h)).mono fun _ hs => not_not.mpr hs⟩
  | and a b => by
    obtain ⟨hapos, haneg⟩ := a.eventually_decided v
    obtain ⟨hbpos, hbneg⟩ := b.eventually_decided v
    refine ⟨fun ⟨ha, hb⟩ => (hapos ha).and (hbpos hb), fun h => ?_⟩
    rcases not_and_or.mp h with ha | hb
    · exact (haneg ha).mono fun _ hs hab => hs hab.1
    · exact (hbneg hb).mono fun _ hs hab => hs hab.2
  | or a b => by
    obtain ⟨hapos, haneg⟩ := a.eventually_decided v
    obtain ⟨hbpos, hbneg⟩ := b.eventually_decided v
    refine ⟨fun h => h.elim (fun ha => (hapos ha).mono fun _ => Or.inl)
      (fun hb => (hbpos hb).mono fun _ => Or.inr), fun h => ?_⟩
    obtain ⟨ha, hb⟩ := not_or.mp h
    exact ((haneg ha).and (hbneg hb)).mono fun _ ⟨hsa, hsb⟩ hab => hab.elim hsa hsb

/-- **Transfer.** A quantifier-free statement true for all real tuples is true
for all hyperreal tuples (Keisler's Axiom E, for field operations and `√`). -/
theorem transfer {n : ℕ} (φ : Formula n) (holdsReal : ∀ v : Fin n → ℝ, φ.HoldsReal v)
    (v : Fin n → Number) : φ.HoldsHyper v := by
  by_contra fails
  obtain ⟨s, hs⟩ := ((φ.eventually_decided v).2 fails).exists
  exact hs (holdsReal _)

end AlgebraicTransfer
