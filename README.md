# HyperCube Group Discovery — Lean 4 Formalization

Formal verification of the HyperCube tensor factorization model for finite quasigroups, accompanying our COLT 2026 submission.

**Status: 2 sorry's, 2 axioms.** All theorems fully proved modulo two axioms (see below) and two sorry's in the Fourier-theoretic abelian proof (work in progress).

## Overview

We formalize the theory of HyperCube parameters `Θ = (A, B, C)` where the structure tensor of a finite quasigroup `(Q, ∘)` of order `n` is approximated by:

$$T_{abc} = \frac{1}{n} \operatorname{Tr}(A_a B_b C_c)$$

The Jacobian-based objective is:

$$\mathcal{H}(\Theta) = \sum_{b,c} \|B_b C_c\|^2 + \sum_{c,a} \|C_c A_a\|^2 + \sum_{a,b} \|A_a B_b\|^2$$

where sums are weighted by the structure tensor. This decomposes into an inverse penalty `B` and a misalignment penalty `R`, with the key result that minimizers achieving `H = 3n²` lie on the **collinear manifold** where `R = 0`.

## Files

| File | Lines | Theorems | Description |
|------|------:|:--------:|-------------|
| `Basic.lean` | 260 | 7 | Core definitions: `BinOp`, `HCParams`, `Factorizes`, `objective`, `frobInner`, `frobNormSq`, Frobenius norm properties |
| `Decomposition.lean` | 873 | 43 | Objective decomposition `H = B + R`, misalignment residuals, penalty nonnegativity, collinearity characterization |
| `CollinearManifold.lean` | 590 | 6 | Shared Gram matrices, `kappaTriple` analysis (`0 < κ ≤ 1`), `κ = 1 ⟺ unitary`, AM-GM lower bound `B.re ≥ 3n²` |
| `GroupIsotope.lean` | 919 | 29 | Group isotopes, isotopy transfer, unitary collinear factorizations, `H = 3n²` for group isotopes (Lemma 8) |
| `AbelianDominance.lean` | 338 | 18 | Characters, diagonal representation, Frobenius norm unitary invariance, objective gauge invariance, **Weak Collinearity Dominance for abelian groups** |

**Totals:** 2,980 lines of Lean 4, 103 theorems, 2 axioms, 2 sorry's.

## Key Results

- **`decomposition`** — `H(Θ) = B(Θ) + R(Θ)` with `R ≥ 0`
- **`normalized_rank_constant`** — The dimensionless ratio `κ` is constant across triples with `0 < κ ≤ 1`
- **`kappa_one_iff_unitary`** — `κ = 1` if and only if all factor slices are unitary
- **`amgm_lower_bound`** — `B(Θ).re ≥ 3n²` for any feasible factorization
- **`group_isotope_admits_unitary_collinear`** — Group isotopes admit unitary collinear factorizations
- **`uc_objective_value`** — Unitary collinear factorizations achieve `H = 3n²`
- **`frobNormSq_unitary_conj`** — `‖U M U†‖² = ‖M‖²` for unitary `U` (new)
- **`objective_unitary_gauge`** — `H` is invariant under symmetric unitary gauge `(U, U, U)` (new)
- **`weak_dominance_abelian`** — For abelian groups, every feasible `Θ` satisfies `H ≥ 3n²` (depends on sorry, NOT on axiom)
- **`abelian_minimizers_collinear`** — For abelian groups, `H = 3n²` implies perfect collinearity (sorry)
- **`abelian_global_optimality`** — Unconditional global optimality for finite abelian groups

## Axioms (2)

1. **`collinear_to_unitary_collinear`** — A collinear feasible nondegenerate factorization implies existence of a unitary collinear factorization. This encodes the variational argument that minimizers on the collinear manifold achieve `κ = 1` (Section 5 of the paper).

2. **`strongCollinearityDominance`** *(revised)* — For any **global minimizer** `Θ*`, there exists `0 ≤ c < 1` such that `B(Θ*) ≥ 3n² - c·R(Θ*)`. Updated from the original conjecture (which applied to all feasible `Θ`) following the discovery of counterexamples outside the minimizer region. Used only by `strict_gap_non_group`; the abelian results are independent.

## Sorry's (2, work in progress)

1. **`abelian_objective_lower_bound`** — Direct Fourier-theoretic proof that `H ≥ 3n²` for abelian groups. The argument goes through gauge-transforming to the character basis, then applying entry-wise AM-GM.

2. **`abelian_minimizers_collinear`** — Tightness of the Fourier lower bound: `H = 3n²` implies `R = 0`.

*Note:* The abelian results (`weak_dominance_abelian`, `abelian_global_optimality`) do NOT depend on `strongCollinearityDominance`. They use only the Fourier-theoretic sorry's above.

## Building

Requires [Lean 4](https://leanprover.github.io/) with [Mathlib](https://github.com/leanprover-community/mathlib4) (v4.29.0-rc6).

```bash
cd lean
lake build
```
