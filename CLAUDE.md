see @Readme.md

│   Concept    │     Mathlib API     │       File       │
│ Null sets / measure-zero sets  │ NullMeasurableSet, μ s = 0  Mathlib/MeasureTheory/Measure/NullMeasurable.lean
├─────┼──────┼──────┤
│ Almost everywhere / almost  │ Measure.ae, ∀ᵐ x ∂μ, p x, f  │ Mathlib/MeasureTheory/OuterMeasure/AE.lean     │
│ surely       │ =ᵐ[μ] g       │               │
├─────┼──────┼──────┤
│ Probability measure (total  │ IsProbabilityMeasure μ    │ Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean │
│ mass 1)      │         │               │
├─────┼──────┼──────┤
│ Borel–Cantelli, SLLN,    │ dedicated files     │ Mathlib/Probability/            │
│ independence       │         │               │
└─────┴──────┴──────┘

Key notations:
- ∀ᵐ x ∂μ, p x  — "for almost every x"
- ᵐ  in ∀ᵐ  just notation name: stands for "almost" allMost (from Latin "magis") wrt ∂μ, μ the measure
-  ∫ f ∂μ ("integral of f with respect to μ")
- f = g modulo µ    — "f equals g almost everywhere with respect to measure μ"
- f =ᵐ[μ] g    — "f equals g almost everywhere"
- ae_iff    — (∀ᵐ a ∂μ, p a) ↔ μ {a | ¬p a} = 0
- mem_ae_iff_prob_eq_one — for probability measures, a.e. ↔ prob = 1