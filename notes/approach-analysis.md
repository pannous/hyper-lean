# Hyperreal Implementation Approaches — Analysis & Recommendation

## Overview

This project has ~15 Lean 4 files exploring different ways to represent hyperreal numbers, plus a working Julia reference implementation (`hyper.jl`). The approaches cluster into 5 families.

## Approach Families

### 1. List-Based: `List (ℚ × ℚ)` — coefficient × exponent pairs
**Files:** HyperList, HyperGeneral (quotient), HyperQuotient, HyperReal (Float)

Direct port of the Julia approach. A hyperreal is a sparse polynomial in ε/ω:
```
3 + 2ε - ω² = [(3,0), (2,-1), (-1,2)]
```
- HyperGeneral wraps this in a `Quotient` for proper equality via simplification
- HyperReal uses `Float` for practical computation
- HyperGeneral is marked "currently best" in the codebase

### 2. Axiomatic (Keisler-style): opaque type + axioms
**Files:** HyperKeisler, HyperKeisler1, HyperKeisler2, HyperKeislerGeneral

Declares `Hyperreal` as an abstract type with axioms (ordered field extension, ε existence, transfer principle). Mathematically rigorous but entirely noncomputable — cannot evaluate `ε + 1`.

### 3. Function-Based: `ℤ → ℚ` with finite support
**Files:** HyperFun (750 lines, most developed), HyperFin (Finsupp, abandoned), HyperMap (RBMap, minimal)

Represents a hyperreal as a function from exponents to coefficients. HyperFun is the most developed file overall. HyperFin tried Lean's `Finsupp` but hit proof complexity walls.

### 4. Fixed-Component: `(ℚ/ℝ, ℚ/ℝ, ℚ/ℝ, Bool)`
**Files:** HyperEasy, HyperQ, Hyper1

Splits into real_part + epsilon_part + infinite_part + exceptional flag. Simple but limited to first-order terms — can't represent `ε²`, `ω³`, etc.

### 5. Julia Reference: `Vector{(ComplexF64, Float32)}`
**File:** hyper.jl (~960 lines)

Working, tested implementation with full arithmetic, Taylor-series transcendentals, derivatives, integration, Dirac delta. The gold standard for "what should work."

## Comparison Matrix

| Criterion | List/Quotient | Axiomatic | Function | Fixed-Component | Julia |
|-----------|:---:|:---:|:---:|:---:|:---:|
| Executable / computable | ✓ | ✗ | partial | ✓ | ✓ |
| Arbitrary orders (ε², ω³…) | ✓ | ✓ | ✓ | ✗ | ✓ |
| Decidable equality | ✓ (via simplify) | by axiom | ✗ | ✓ (with ℚ) | ✗ |
| Proof-friendly | medium | high | low | medium | N/A |
| Complexity of proofs | medium | deferred | high | low | N/A |
| Closest to Julia model | ✓✓ | ✗ | ✓ | ✗ | — |

## Recommendation: List/Quotient with ℚ (HyperGeneral approach)

**The quotient-of-lists approach (HyperGeneral) is the best path forward.** Here's why:

### Why not Axiomatic?
Elegant on paper but you can never *run* anything. You can't evaluate `sin(ε)` or test derivatives numerically. The whole point of this project is to *compute* with hyperreals, not just prove abstract theorems. Axioms are a dead end for an executable algebra.

### Why not Function-Based?
`ℤ → ℚ` can't decide equality (you'd need to check infinitely many exponents). HyperFun works around this with an `order` bound, but that's a hack that doesn't compose well with Lean's type system. The Finsupp approach (HyperFin) was the right idea but Lean's Finsupp proofs are brutal — it was abandoned for good reason.

### Why not Fixed-Component?
Too restrictive. The Julia implementation freely uses `ε²`, `ω³`, mixed orders, etc. A 3-component struct can't represent the full algebra. It's fine for basic calculus demos but not for the ambitions of this project.

### Why List/Quotient wins:
1. **Direct translation of the Julia model** — same `(coeff, exponent)` pairs, same simplification logic
2. **Executable** — you can `#eval` expressions, test numerically, port Julia tests
3. **Decidable equality** — simplify both sides, compare sorted lists (with ℚ coefficients)
4. **Arbitrary orders** — naturally handles ε², ω³, mixed terms
5. **Proof-tractable** — quotient types are well-supported in Lean/Mathlib; the equivalence relation (same after simplification) is straightforward
6. **Already the most complete** — HyperGeneral compiles and has working instances

### Specific improvements to HyperGeneral:
- Use `ℤ` for exponents (not `ℚ`) — integer exponents suffice and simplify ordering
- Store terms sorted by exponent for canonical form (avoids needing quotient at all)
- Port the Julia test suite as `#eval`-based checks
- Add `DecidableEq` instance via sorted canonical form
- Implement `inv` via Newton iteration (as Julia does)
- Add `sin`/`cos`/`exp`/`log` via Taylor series

### Long-term:
Once the list approach is solid and tested, consider migrating the internal representation to `Finsupp ℤ ℚ` for Mathlib compatibility — but only after the API is stable. The list version serves as the executable prototype; Finsupp can be the "verified backend" later.

## Summary

**HyperGeneral (quotient of lists with ℚ coefficients) is the sweet spot** — it's the only approach that is simultaneously executable, extensible to arbitrary orders, proof-friendly, and a faithful port of the working Julia code. Focus energy here.
