# HyperCube Group Discovery — Lean 4 Formalization

Formal verification of the HyperCube tensor factorization model for finite quasigroups, accompanying our NeurIPS 2026 submission.

This repository provides an end-to-end Lean 4 mechanization of the manuscript's core landscape results, including the orthogonal decomposition of the objective, the Matrix AM-GM inequality, and the global optimality of group isotopes. 

## Named Axiom-Free Theorems

For each named theorem below, `#print axioms <name>` yields the standard Lean background list `[propext, Classical.choice, Quot.sound]` only — no project-specific axioms are used.

| Manuscript | Lean name | File |
|---|---|---|
| Lemma 16 (Matrix AM-GM) | `lemma16_matrix_amgm` | `MatrixAMGM.lean` |
| Lemma 16 equality side | `lemma16_matrix_amgm_equality` | `MatrixAMGM.lean` |
| Theorem 4 (UC ⟺ Group Isotope) | `theorem4_unitary_collinearity_iff_group_isotope` | `GroupIsotope.lean` |
| Theorem 9 (Universal Lower Bound) | `theorem9_absolute_feasible_bound_lower` | `GroupIsotope.lean` |
| Theorem 9 (Equality Rigidity) | `theorem9_absolute_feasible_bound_rigidity` | `GroupIsotope.lean` |
| Theorem 10 (Global Optimality) | `theorem10_global_optimality_dichotomy` | `GroupIsotope.lean` |
| Theorem 10 Case 2 (Strict Gap) | `strict_gap_non_group_unconditional` | `GroupIsotope.lean` |
| Theorem 18 (Regularized Existence)| `theorem18_regularized_existence` | `Tikhonov.lean` |

## Gauge-Quotient Theorems (Axiom-Free)

The landscape results above are also formally lifted to the combined gauge quotient `FeasibleCombinedGaugeQuotient n f` in `Coercivity.lean`:

- `theorem9_absolute_feasible_bound_lower_feasibleQuotient` — `ℋ(Θ).re ≥ 3n²` on quotient
- `theorem10_case2_strict_gap_non_group_feasibleQuotient` — for non-group `f`, strict `>` on quotient
- `isOptimal_iff_unitaryCollinear_feasibleQuotient` — Theorem 9 on quotient
- `exists_isOptimal_iff_group_isotope_feasibleQuotient` — Theorem 10 on quotient
- `feasibleQuotient_optimal_or_strict` — global dichotomy

## Overview

We formalize the theory of HyperCube parameters `Θ = (A, B, C)` where the structure tensor of a finite quasigroup `(Q, ∘)` of order `n` is approximated by:

$$T_{abc} = \frac{1}{n} \operatorname{Tr}(A_a B_b C_c)$$

The Jacobian-based objective is:

$$\mathcal{H}(\Theta) = \sum_{b,c} \|B_b C_c\|^2 + \sum_{c,a} \|C_c A_a\|^2 + \sum_{a,b} \|A_a B_b\|^2$$

where sums are weighted by the structure tensor. This decomposes into an inverse-scale penalty `ℬ_δ` and a misalignment penalty `ℛ_δ`, with the key result that minimizers achieving `ℋ = 3|δ|= 3n²` lie on the **collinear manifold** where `ℛ_δ = 0`.

## Files

| File | Lines | Description |
|------|------:|-------------|
| `Basic.lean` | 260 | Core definitions: `BinOp`, `HCParams`, `Factorizes`, `objective`, `frobInner`, `frobNormSq` |
| `Decomposition.lean` | 869 | Objective decomposition `ℋ = ℬ_δ + ℛ_δ`, misalignment residuals |
| `CollinearManifold.lean` | 589 | Shared Gram matrices, `kappaTriple` analysis, `κ = 1 ⟺ unitary`, AM-GM lower bound |
| `GroupIsotope.lean` | 1308 | Group isotopes, isotopy transfer, unitary collinear factorizations, `ℋ = 3n²` for group isotopes |
| `Abelian.lean` | 312 | Diagonal rep, full U(n)³ gauge invariance, cyclic group instance |
| `MatrixAMGM.lean` | 297 | Matrix AM-GM `‖XY‖² + ‖YZ‖² + ‖ZX‖² ≥ 3‖tr(XYZ)‖^{4/3}` and equality rigidity |
| `BlockCyclic.lean` | 519 | Block-cyclic 3n×3n matrix construction; structural equivalences |
| `Spectral.lean` | 1332 | Schur triangulation, trace bounds, equality cases |
| `Plancherel.lean` | 387 | Plancherel infrastructure: ℋ = mass matrix form, Fourier sums |
| `PontryaginBridge.lean` | 516 | `IsAbelianGroup.toAddCommGroup`, `characterBasis`, `abelian_admits_diagRep_optimum` |
| `ActiveSubspace.lean` | 740 | Active-subspace machinery |
| `ActiveSubspaceConstruction.lean` | 851 | Explicit discharge of `collinear_to_unitary_collinear` for full-rank cases |
| `ActiveSubspaceGeneric.lean` | 559 | Generic `gramOf` machinery |
| `Tikhonov.lean` | 639 | HCParams normed/finite-dim structure; Weierstrass + regularized existence theorems |
| `Coercivity.lean` | 4056 | Full gauge group structure, invariances, gauge orbit + setoid + quotient + lifted predicates |

**Totals:** ~13,250 lines of Lean 4, **1 axiom**, **0 `sorry`s**. Builds green throughout.

## Core Formalized Results

The codebase mechanizes the following major theoretical claims from the manuscript:

**1. Orthogonal Decomposition (Section 3)**
* **`lemma1_decomposition`** (Lemma 1): Proves the objective rigorously splits into an inverse-scale penalty and a misalignment penalty (`ℋ = ℬ_δ + ℛ_δ`), establishing that `ℋ ≥ ℬ_δ` with equality if and only if perfect collinearity holds (`ℛ_δ = 0`).

**2. Spectral Geometry of the Collinear Manifold (Section 4)**
* **`lemma2_shared_gram_matrices`** (Lemma 2): Proves that under perfect collinearity, the parameters share index-independent, trace-n PSD Gram matrices (`X`, `Y`, `Z`).
* **`lemma3_normalized_rank_constant`** (Lemma 3): Establishes that the normalized rank ratio `κ` is constant across the support, and that `κ ≤ 1`.
* **`lemma6_collinear_lower_bound`** (Lemma 6): Proves the absolute lower bound `ℬ_δ ≥ 3|δ|` via the scalar AM-GM inequality.
* **`theorem7_optimality_within_collinear_manifold`** (Theorem 7): Proves that, restricted to the collinear manifold, the minimum is exactly `3|δ|` and is achieved uniquely by a unitary collinear factorization.

**3. The Group Isotope Equivalence (Section 4)**
* **`collinear_iff_group_isotope`** (Theorem 5): The bidirectional proof establishing that a finite quasigroup admits a nondegenerate collinear factorization *if and only if* it is isotopic to a group. This packages together:
  * **`unitary_collinear_implies_group_isotope`** (Theorem 4 necessity): The necessity direction, built on the `lemma11_synchronization` gauge and `lemma12_synchronized_homomorphism`.
  * **`lemma14_group_isotope_admits_unitary_collinear`** (Lemma 14): The sufficiency direction, constructed explicitly via the `leftRegularRep`.

**4. Global Landscape (Section 6)**
* **`universal_lower_bound_general`**: For **any** binary operation `f` and any feasible Θ, `ℋ(Θ) ≥ 3|δ|`. Proved unconditionally from the Matrix AM-GM lemma.
* **`equality_rigidity_general`**: The equality `ℋ(Θ) = 3|δ|` forces every supported triple `(A_a, B_b, C_{f(a,b)})` to be unitary with `A_a · B_b · C_{f(a,b)} = I`.
* **`equality_rigidity_implies_perfect_collinearity`**: The equality `ℋ(Θ) = 3|δ|` for a feasible nondegenerate Θ implies `ℛ_δ(Θ) = 0`.
* **`strict_gap_non_group_unconditional`** (Theorem 10 Case 2): For any quasigroup `f` that is not a group isotope, every feasible Θ has `ℋ(Θ) > 3|δ|` strictly. 

**5. Matrix AM-GM (`MatrixAMGM.lean`, `BlockCyclic.lean`, `Spectral.lean`)**
* **`lemma16_matrix_amgm`** (**theorem, proved**): For any $X, Y, Z \in \mathbb{C}^{n \times n}$ with $\frac{1}{n}\operatorname{Tr}(XYZ) = 1$, $\|XY\|^2 + \|YZ\|^2 + \|ZX\|^2 \ge 3$. Mechanised end-to-end from `matrix_unitary_schur_form`.
* **`lemma16_matrix_amgm_equality`** (**theorem, proved**): Equality forces $X, Y, Z$ to be unitary and $XYZ = I$. 

## Axioms (1)

The codebase contains zero `sorry`s. The single remaining axiom (`collinear_to_unitary_collinear`) is **manuscript-internal**, not a textbook fact, and is appropriately flagged.

1. **`collinear_to_unitary_collinear`** *(in `GroupIsotope.lean`)* — A collinear feasible nondegenerate factorisation implies the existence of a unitary collinear factorisation.
   * *Context:* Manuscript Theorem 5 / Appendix E (Rigidity of Collinearity). The full proof requires restricting each $A_a, B_b, C_c$ to the column space of the shared Gram $X$ (where $A_a / \sqrt{\alpha_a}$ becomes a partial isometry), then extending to a full unitary on $\mathbb{C}^n$ via Gram-Schmidt. 
   * *Status:* Mechanising this final spatial restriction requires advanced projective unitary gauge transformations. It remains the single axiom in the codebase and only affects the rank-deficient sub-case of Theorem 5. **It does not affect the headline landscape theorems (Theorems 9 and 10), which are fully verified.**

## Scope of Formalization (What is not Mechanized)

This Lean 4 repository focuses strictly on the **algebraic and geometric** properties of the HyperCube model (Sections 3, 4, 6, and Appendices). 

The following manuscript components remain outside the scope of formalization:
* **Hessian eigenvalue analysis (Appendix F.2):** The Laplacian Hessian's spectral gap controls local coercivity; the explicit eigenvalue bounds are not mechanised.
* **Empirical Pareto frontier (Section 5.3):** The observed geometric trade-offs are empirical demonstrations, not formalized theorems.

## Mathlib Upstream Candidates

The codebase contains several pieces of independent interest to the broader Lean / Mathlib community that are fully proved here and would naturally live upstream:

1. **Unitary Schur triangulation** (`matrix_unitary_schur_form`): `∃ U unitary, U†·A·U is upper triangular for any complex A`. Currently absent in Mathlib.
2. **Schur trace bound** (`IsUpperTriangular.norm_trace_cubed_pow_four_le`): `‖Tr(T³)‖⁴ ≤ N·(‖T·T‖²_F)³` for upper triangular `T`. 
3. **Power-mean Hölder bound** (`Real.sum_pow_three_pow_four_le`): `(Σ f_i³)⁴ ≤ N · (Σ f_i⁴)³` for nonneg real `f`.
4. **`AddCommGroup (Fin n)` bridge**: Constructs the abelian-group typeclass directly from a finite quasigroup's cancellation laws (`IsAbelianGroup.toAddCommGroup`).

## Building

Requires [Lean 4](https://leanprover.github.io/) with [Mathlib](https://github.com/leanprover-community/mathlib4) (v4.29.0-rc6).

```bash
cd lean
lake build