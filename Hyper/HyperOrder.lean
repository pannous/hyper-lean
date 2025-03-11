-- /-- The hyperreal numbers ℝ⋆ form a linear ordered field. -/

-- This file should be part of HyperFacts:
-- This file should be independent of the specific implementation
-- The notion .real can be added as alias to any type later on

-- define < and ≤ for hyperreals
-- noncomputable -- because it depends on 'Real.instLinearOrderedField', and it does not have executable code

lemma hyper_le_total (a b : Hyper) : a.real ≤ b.real ∨ b.real ≤ a.real := by
  let or1 := a.real ≤ b.real
  let or2 := b.real ≤ a.real
  apply or.elim (Real.le_total a.real b.real)
  { intro h
    apply or.inl h
  }
  { intro h
    apply or.inr h
  }


lemma hyper_transitivity (a b c : Hyper) (h₁ : a.real < b.real) (h₂ : b.real < c.real) : a.real < c.real := by
    apply lt_trans h₁ h₂
    -- simp only [le];
    cases --h₁
    intro h₁₁;
    apply or.inl (lt_of_lt_of_le h₁₁ (or.elim h₂ id (λ h => h.1)));
    intro h₁₂;
    apply or.elim h₂;
    intro h₂₁;
    apply or.inl (lt_of_le_of_lt h₁₂ h₂₁);
    intro h₂₂;
    cases h₁₂;
    cases h₂₂;
    apply or.inr;
    split;
    assumption;
    apply le_trans h₁₂_right h₂₂_right

lemma hyper_le_antisymm (a b : Hyper) (h₁ : a.real ≤ b.real) (h₂ : b.real ≤ a.real) : a = b := by
  -- intros a b
  simp only [le, lt];
  intro h₁ h₂;
  apply or.elim h₁;
  intro h₁₁;
  apply or.elim h₂;
  intro h₂₁;
  exfalso;
  exact lt_irrefl _ (lt_trans h₁₁ h₂₁);
  intro h₂₂;
  cases h₂₂;
  contradiction;
  intro h₁₂;
  apply or.elim h₂;
  intro h₂₁;
  cases h₁₂;
  contradiction;
  intro h₂₂;
  cases h₁₂;
  cases h₂₂;
  congr;
  exact le_antisymm h₁₂_left h₂₂_left;
  exact le_antisymm h₁₂_right h₂₂_right
  -- intros a b;
  -- simp only [le, lt];
  -- intro h₁ h₂;
  -- apply or.elim h₁;
  -- intro h₁₁;
  -- apply or.elim h₂;
  -- intro h₂₁;
  -- exfalso;
  -- exact

-- set_option tactic.simp.trace true
-- set_option trace.class_instances true
-- set_option trace.Debug.Meta.Tactic.simps true

lemma hyper_transitivity {a b c : Hyper} :
  (a ≤ b ∧ b ≤ c) → a ≤ c := by {
  intros h

  match h with
  | ⟨h1, h2⟩ =>
    -- Apply transitivity logic here
    unfold LinearOrder.le at *
  -- cases h with h1 h2
  -- unfold LinearOrder.le at *,
  -- Example simplification, needs actual logic based on Hyper properties
    simp [h1, h2]
  -- Add real reasoning
  simp only [LinearOrder.le] at *
  -- Insert the logic for transitivity

}

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  apply Or.inr
  assumption
  apply Or.inl
  assumption

lemma hyper_le_antisymm {a b : Hyper} : a ≤ b ∧ b ≤ a → a = b := by
  intros h
  cases h
  apply Hyper.ext
  { show a.real = b.real; sorry }
  { show a.epsilon = b.epsilon; sorry }
  { show a.infinite = b.infinite; sorry }
  --
  --  with
  -- | h1 h2
  -- unfold LinearOrder.le at *,
  -- -- Your logic here to prove equality
  -- sorry

lemma hyper_le_total {a b : Hyper} :
  a ≤ b ∨ b ≤ a := by {
  unfold LinearOrder.le
  -- Insert the logic for total ordering
  sorry
}

instance : LinearOrder Hyper where
  le a b := a.real < b.real || (a.real = b.real && a.epsilon < b.epsilon) || (a.real = b.real && a.epsilon = b.epsilon && a.infinite ≤ b.infinite)
  lt a b := a.real < b.real || (a.real = b.real && a.epsilon < b.epsilon) || (a.real = b.real && a.epsilon = b.epsilon && a.infinite < b.infinite)
  le_refl a := by simp [le]
  le_trans := hyper_transitivity
  le_antisymm := hyper_le_antisymm
  le_total := hyper_le_total
  -- decidable_le := by
  --   intros a b;
  --   simp only [le];
  --   sorry
    -- apply_instance
  -- decidable_lt := by
    -- apply_instance -- assuming decidable instances on ℝ are available
