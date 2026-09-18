# Current manuscript and publication status

The current probability manuscript is `algebraic-probability.tex`, titled
**Algebraic Infinitesimal Probability: Geometric Content, Conditioning, and
Certified Precision**. Its rendered PDF is
`../output/pdf/algebraic-probability.pdf`.

This is a working draft for mathematical review, not a submitted paper.
It consolidates the exact field, normalized integral, square/cube and
disk/ball examples, point/dot/halo distinction, and algebraic O notation.
It states explicitly which results are formalized and which remain open.

## Initial publication assessment

It is worth writing and circulating as a carefully scoped exposition and
formalization project. Readiness for a research-journal submission depends
on identifying a defensible contribution beyond the known ingredients and
establishing a sufficiently useful geometric event domain.

The prior-work check found a direct connection: our content is
`ν_ε(K)=ε^d g_K(ε⁻¹)`, where `g_K` is the classical Wills polynomial.
See [Hernández Cifre and Yepes Nicolás](https://webs.um.es/jesus.yepes/publicaciones_files/paper_WillsFunctional.pdf),
equation (1.4). This polynomial must not be presented as newly discovered.
Infinitesimal probabilities and normalized numerosities also have an
established literature; see
[Benci, Horsten, Wenmackers](https://arxiv.org/abs/1106.1524) and
[Benci, Bottazzi, Di Nasso](https://arxiv.org/abs/1212.6201).
The search was an initial comparison, not a proof of originality or an
exhaustive literature review.

The potential contribution is the combination of a small exact field,
explicit geometric probability contexts, certified precision rules, and
Lean-checked normalization and conditioning. The current draft makes that
limited case without claiming a new replacement for probability theory.

Before submission:

1. Decide whether the paper is primarily exposition/formalization or a new
   general geometric theorem, and make the contribution explicit.
2. For a general geometric claim, prove positivity and compatibility under
   common refinements on a precisely specified event algebra. The current
   checked finite contexts are not yet this global construction.
3. Expand the literature comparison, including previous uses of Wills
   polynomials in probability and algebraic infinitesimal measures.
4. Obtain independent mathematical review, settle authorship and the final
   claims, and choose a suitable venue based on the resulting paper.

## Older manuscript

`hyperreals.tex`, `hyperreals-light.tex`, and their PDFs are historical
introductory drafts. They have not been comprehensively corrected and
should not be submitted as the current results. In particular:

- They identify finite Laurent polynomials with a field; exact mixed
  inverses require rational functions or another suitable extension.
- Their transfer axiom does not hold in the current field R(ε).
- Their broad claim that every construction has an audited HyperList
  counterpart is not supported by the present trust boundary.
- Their expectation and conditioning readiness claims predate the current
  normalized finite-observable API.
- Their general geometric, calculus, and publication claims require a
  separate review, not just appending the new examples.

The focused probability draft supersedes those probability claims while
preserving the historical sources for a later full rewrite.

## Rebuild

From the repository root:

```sh
bash paper/build_probability.sh
```

The build runs LaTeX twice, checks unresolved references and overfull boxes,
and puts auxiliary files under `tmp/pdfs/probability-build/`. Run
`bash test.sh` for the separate Lean regression suite and axiom audit.
