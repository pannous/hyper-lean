# Future extension: computable symbolic roots via resultants

Status: NOT needed for current proofs (field, roots, transfer are all proved
semantically in `Hyper/HyperAlgebraic.lean`). Needed only to *compute*
(`#eval` / `native_decide`) with root expressions like √ω + √(1+ω).

## Idea
Represent an element as (defining polynomial P(ω, Y) over ℚ(ω), which root).
- Resultant: Res(P,Q) = aᵐbⁿ∏(αᵢ−βⱼ) = det(Sylvester matrix); zero iff common root.
- Sum:     α+β is a root of Res_Y(P(Y), Q(Z−Y)).
- Product: αβ  is a root of Res_Y(P(Y), Yᵐ·Q(Z/Y)).
- Inverse: reverse polynomial. Root: P(Yⁿ).
- Examples: √2+√3 → Z⁴−10Z²+1;  √ω+√(1+ω) → Z⁴−2(2ω+1)Z²+1.
- Equality x = y: defining polynomial R of x−y; R(ω,0) ≠ 0 ⇒ x ≠ y; else decide
  whether the selected root is 0 via Sturm root counting over ℚ(ω) (signs of
  polynomials in ω = sign of leading coefficient, i.e. our order).

## Hard parts
- Root selection ("k-th real root of R(s,·) for large s") through each operation.
- Squarefree/gcd preprocessing (Res ≡ 0 on shared factors).
- Degree blow-up: degrees multiply (√2+√3+√5 already degree 8).
- Soundness bridge: prove the symbolic value equals the germ in `HyperAlgebraic.Number`.

## Available
Mathlib `Polynomial.resultant` (computable `def`, Sylvester determinant):
`Mathlib/RingTheory/Polynomial/Resultant/Basic.lean`.

## Trigger to start
When a task needs evaluating/deciding concrete root expressions, or when
real-closedness (roots of arbitrary odd-degree polynomials) is tackled —
both share the root-selection machinery.
