# HyperCube Group Discovery — Lean 4 Formalization

Formal verification of the HyperCube tensor factorization model for finite quasigroups, accompanying our NeurIPS 2026 submission.

**Status: Theorems 8, 9, 10, 16 (and Theorem 4 unitary case) verified unconditionally.** The single remaining axiom is `collinear_to_unitary_collinear` for the κ<1 sub-case of Theorem 5 (Appendix E's subspace-restriction argument); the κ=1 sub-case is fully discharged. The headline result — Theorem 10, resolving the original HyperCube conjecture (Huh 2025, Conjecture 6.1) — routes through Theorem 4, not Theorem 5, and is therefore unconditional.

## Named axiom-free theorems

For each named theorem below, `#print axioms <name>` yields the standard
list `[propext, Classical.choice, Quot.sound]` only — no project axioms.

| Manuscript | Lean name | File |
|---|---|---|
| Lemma 28 (Matrix AM-GM) | `lemma28_matrix_amgm` | `MatrixAMGM.lean` |
| Lemma 28 equality side | `lemma28_matrix_amgm_equality` | `MatrixAMGM.lean` |
| Theorem 4 (UC ⟺ Group Isotope) | `theorem4_unitary_collinearity_iff_group_isotope` | `GroupIsotope.lean` |
| Theorem 8 (Universal Lower Bound) | `theorem8_universal_lower_bound` | `GroupIsotope.lean` |
| Theorem 9 (Equality Rigidity) | `theorem9_equality_rigidity` | `GroupIsotope.lean` |
| Theorem 10 (Global Optimality) | `theorem10_global_optimality` | `GroupIsotope.lean` |
| Theorem 10 case 2 (strict gap) | `strict_gap_non_group_unconditional` | `GroupIsotope.lean` |
| Theorem 16 (Tikhonov Existence) | `theorem16_tikhonov_existence` | `Tikhonov.lean` |

Theorem 10 — the resolution of Huh (2025) Conjecture 6.1 — depends only on standard Lean axioms.

## Gauge-quotient theorems (axiom-free)

The same landscape results lifted to the combined gauge quotient `FeasibleCombinedGaugeQuotient n f`:

- `theorem8_universal_lower_bound_feasibleQuotient` — `objective.re ≥ 3n²` on quotient
- `strict_gap_non_group_feasibleQuotient` — for non-group `f`, strict `>` on quotient
- `isOptimal_iff_unitaryCollinear_feasibleQuotient` — Theorem 9 on quotient
- `exists_isOptimal_iff_group_isotope_feasibleQuotient` — Theorem 10 on quotient
- `feasibleQuotient_optimal_or_strict` — dichotomy

All in `Coercivity.lean`.

## Overview

We formalize the theory of HyperCube parameters `Θ = (A, B, C)` where the structure tensor of a finite quasigroup `(Q, ∘)` of order `n` is approximated by:

$$T_{abc} = \frac{1}{n} \operatorname{Tr}(A_a B_b C_c)$$

The Jacobian-based objective is:

$$\mathcal{H}(\Theta) = \sum_{b,c} \|B_b C_c\|^2 + \sum_{c,a} \|C_c A_a\|^2 + \sum_{a,b} \|A_a B_b\|^2$$

where sums are weighted by the structure tensor. This decomposes into an inverse penalty `B` and a misalignment penalty `R`, with the key result that minimizers achieving `H = 3n²` lie on the **collinear manifold** where `R = 0`.

## Files

| File | Lines | Description |
|------|------:|-------------|
| `Basic.lean` | 260 | Core definitions: `BinOp`, `HCParams`, `Factorizes`, `objective`, `frobInner`, `frobNormSq` |
| `Decomposition.lean` | 873 | Objective decomposition `H = B + R`, misalignment residuals |
| `CollinearManifold.lean` | 590 | Shared Gram matrices, `kappaTriple` analysis, `κ = 1 ⟺ unitary`, AM-GM lower bound |
| `GroupIsotope.lean` | 1128 | Group isotopes, isotopy transfer, unitary collinear factorizations, `H = 3n²` for group isotopes |
| `AbelianDominance.lean` | 445 | Characters, diagonal rep, abelian dominance results |
| `MatrixAMGM.lean` | 272 | Matrix AM-GM `‖XY‖² + ‖YZ‖² + ‖ZX‖² ≥ 3‖τ_n(XYZ)‖^{4/3}` and equality rigidity |
| `BlockCyclic.lean` | 520 | Block-cyclic 3n×3n matrix construction; structural equivalences |
| `Spectral.lean` | 1332 | Schur triangulation, trace bounds, equality cases — Tier 2A backbone |
| `Plancherel.lean` | 395 | Plancherel infrastructure: H = mass matrix form, Fourier sums |
| `PontryaginBridge.lean` | 492 | `IsAbelianGroup.toAddCommGroup`, `characterBasis`, `abelian_admits_diagRep_optimum` |
| `ActiveSubspace.lean` | 740 | Active-subspace machinery (κ<1 partial infrastructure) |
| `ActiveSubspaceConstruction.lean` | 851 | κ=1 discharge of `collinear_to_unitary_collinear` |
| `ActiveSubspaceGeneric.lean` | 559 | Generic `gramOf` machinery |
| `Tikhonov.lean` | 626 | Tier 3A: HCParams normed/finite-dim structure; Weierstrass + Tikhonov existence theorems (Theorem 16) |
| `Coercivity.lean` | 3671 | Tier 3B: full gauge group structure (gaugeAction, unitaryConjAction, combinedGauge), invariances, LinearMap/CLE packagings, gauge orbit + setoid + quotient + lifted predicates, AM-GM at quotient |

**Totals:** ~12,750 lines of Lean 4, **1 axiom** (`collinear_to_unitary_collinear` κ<1), **0 `sorry`s**, zero open-conjecture commitments. Build green throughout.

**Tier 2A complete:** matrix AM-GM (both sides) and Schur triangulation are proved theorems. **Tier 3A complete:** HCParams full normed/finite-dim structure + Tikhonov existence (seven existence theorems). **Tier 3C complete:** Pontryagin bridge + constructive abelian UC via diagRep. **Tier 3B substantial:** gauge group structure mechanised (Section 2.4 + Appendix F infrastructure). **Tier 2B partial:** κ=1 case discharged; κ<1 remains as the single open axiom.

## Core Formalized Results

The codebase mechanizes the following major theoretical claims from the manuscript:

**1. Orthogonal Decomposition (Section 3)**
* **`decomposition`** (Lemma 3): Proves the objective rigorously splits into an inverse-scale penalty and a misalignment penalty (`H = B + R`), establishing that `H ≥ B` with equality if and only if perfect collinearity holds (`R = 0`).

**2. Spectral Geometry of the Collinear Manifold (Section 5)**
* **`shared_gram_matrices`** (Lemma 10): Proves that under perfect collinearity, the parameters share index-independent, trace-n PSD Gram matrices (`X`, `Y`, `Z`).
* **`normalized_rank_constant`** (Lemma 11): Establishes that the normalized rank ratio `κ` is constant across the support, and that `κ ≤ 1`.
* **`amgm_lower_bound`** (Lemma 13): Proves the absolute lower bound `B ≥ 3n²` via the scalar AM-GM inequality.
* **`collinear_manifold_optimality`** (Theorem 14): Proves that, restricted to the collinear manifold, the minimum is exactly `3n²` and is achieved uniquely by a unitary collinear factorization.

**3. The Group Isotope Equivalence (Section 4)**

* **`collinear_iff_group_isotope`** (Theorem 12): The bidirectional proof establishing that a finite quasigroup admits a nondegenerate collinear factorization  *if and only if* it is isotopic to a group. This packages together:
  * **`unitary_collinear_implies_group_isotope`** (Theorem 7): The necessity direction, built on the `synchronization` gauge (Lemma 5) and `synchronized_homomorphism` (Lemma 6).
  * **`group_isotope_admits_unitary_collinear`** (Lemma 8): The sufficiency direction, constructed explicitly via the `leftRegularRep`.

3. The Group Isotope Equivalence (Section 4)

collinear_iff_group_isotope (Theorem 12): The bidirectional proof establishing that a finite quasigroup admits a nondegenerate collinear factorization if and only if it is isotopic to a group (Collinearity ⟺ Group Isotope). This packages together:

unitary_collinear_implies_group_isotope (Theorem 7): The necessity direction, establishing that unitary collinearity forces associativity via the synchronization gauge (Lemma 6) and synchronized_homomorphism (Lemma 6).

group_isotope_admits_unitary_collinear (Lemma 8): The sufficiency direction, constructing the exact unitary collinear factorization explicitly via the left-regular representation.

**4. Global Landscape and Dominance (Section 6)**
* **`weakDominance_general`** (`AbelianDominance.lean`, **NEW**): For **any** binary operation `f` and any feasible Θ, `H(Θ) ≥ 3n²`. Strictly stronger than the manuscript's Conjecture 17 (which restricts to group isotopes); needs only feasibility per supported triple. Proved from the matrix AM-GM lemma in `MatrixAMGM.lean`.
* **`dominanceEquality_general`** (`AbelianDominance.lean`, **NEW**): The equality `H = 3n²` forces every supported triple `(A_a, B_b, C_{f(a,b)})` to be unitary with `A_a · B_b · C_{f(a,b)} = I`. Strictly stronger than `R = 0`.
* **`dominance_equality_implies_perfect_collinearity`** (**NEW**): The equality `H = 3n²` for a feasible nondegenerate Θ implies `R(Θ) = 0`. Direct corollary of the above.
* **`strict_gap_non_group`** (`GroupIsotope.lean`, **rewritten unconditional**): For any quasigroup `f` that is not a group isotope, every feasible Θ has `H > 3n²` strictly. Now unconditional, derived from the equality rigidity. The previous Conjecture-19-conditional version has been replaced; the `strongCollinearityDominance` axiom is removed.
* **`abelian_global_optimality`**: For finite abelian groups, both the existence of an optimal unitary collinear factorisation at `H = 3n²` and the universal lower bound are now derived (modulo `matrix_amgm_at_one`).
* **`abelian_minimizers_collinear`**: Tightness for abelian groups is now a thin wrapper around `dominance_equality_implies_perfect_collinearity`.

**5. Plancherel infrastructure (`Plancherel.lean`, unconditional)**
* **`H_eq_mass_matrix_form`**: For any quasigroup, `H = (1/n) [Tr(R_A·L_B) + Tr(R_B·L_C) + Tr(R_C·L_A)]`. Pure algebra; no abelian assumption.
* **`mass_R_eq_fourier_sum`, `mass_L_eq_fourier_sum`**: Plancherel identities for the right/left Gram mass matrices, parameterised on a `CharacterBasis`. Useful structural Fourier infrastructure independent of any conjecture.

**6. Matrix AM-GM (`MatrixAMGM.lean`, `BlockCyclic.lean`, `Spectral.lean`)**
* **`matrix_amgm_at_one`** (**theorem, proved**): For any `X, Y, Z ∈ ℂ^{n×n}` with `(1/n)·Tr(XYZ) = 1`, `‖XY‖² + ‖YZ‖² + ‖ZX‖² ≥ 3`. **Mechanised end-to-end** from `matrix_unitary_schur_form`.
* **`matrix_amgm_at_one_equality`** (**theorem, proved**): Equality forces `X, Y, Z` unitary and `XYZ = I`. **Mechanised end-to-end** from `matrix_unitary_schur_form` plus the equality cases of triangle, iterated Cauchy-Schwarz, and Schur tightness, plus the cube-roots-of-unity-don't-pair-to-zero argument.

Both sides of the matrix AM-GM lemma are now proved theorems. The proof composes the entire Tier 2A infrastructure (~600 lines across `BlockCyclic.lean`, `Spectral.lean`, `MatrixAMGM.lean`):
* `BlockCyclic.lean` defines the `3n × 3n` block-cyclic matrix `M`, proves `‖M²‖²_F = ‖XY‖² + ‖YZ‖² + ‖ZX‖²`, `Tr(M³) = 3 Tr(XYZ)`, and the structural correspondences `blockCyclicFin_mul_conjTranspose_eq_one_iff` and `blockCyclicFin_cb_eq_one_iff`.
* `Spectral.lean` proves the upper-triangular trace bound `‖Tr(T³)‖⁴ ≤ N (‖T²‖²_F)³` (via triangle, iterated Cauchy-Schwarz, Schur tightness), unitary conjugation invariance, and the equality versions of all three inequalities. The composition lemma `IsUpperTriangular.diagonal_of_chain_eq_at_real_pos` extracts T diagonal of cube roots of unity from chain equality plus `Tr(T^3) = N`. The diagonal lemma `IsUpperTriangular.diagonal_of_sq_offdiag_zero_of_diag_pow_three_one` uses strong induction on `j.val - i.val` and the cube-roots-of-unity-pair-nonzero argument.
* `MatrixAMGM.lean` orchestrates the proof: Schur applied to `blockCyclicFin X Y Z`, equality propagation through the chain, T diagonal of cube roots, then M unitary and M³ = I via the unitary algebra, finally transfer to X, Y, Z via the structural correspondences.

## Axioms (1)

The codebase contains zero `sorry`s. The Conjecture-17 axioms (`abelianWeakDominance`, `abelianDominanceTightness`) and the Conjecture-19 axiom (`strongCollinearityDominance`) have all been removed; their conclusions are now theorems derived from the (now proved) matrix AM-GM lemma. The matrix AM-GM axioms and the Schur triangulation axiom have also been discharged as proved theorems. The single remaining axiom (`collinear_to_unitary_collinear`) is **manuscript-internal**, not a textbook fact, and is appropriately flagged as such.

1. **`collinear_to_unitary_collinear`** *(in `GroupIsotope.lean`, classification: **manuscript-internal**)* — A collinear feasible nondegenerate factorisation implies the existence of a unitary collinear factorisation.
   * *Context:* Manuscript Theorem 21 / Appendix E (Rigidity of Collinearity). This claim is proved in the authors' own manuscript, not in standard external linear-algebra references.
   * *Status:* **Self-referential / manuscript-internal**. The simple "scale each slice by `1/√α_a`" approach (the `rescaleByNorm` helper added in this session) does not work: rescaling by scalars preserves `Factorizes` only when `αβγ = 1` on support (i.e., `κ = 1`), but it does NOT preserve `PerfectCollinearity` even then, because the misalignment residuals scale by `(1/√α_a − 1/α_a)` which is generally nonzero. The full proof requires the active-subspace argument: restrict each `A_a, B_b, C_c` to the column space of the shared Gram `X` (where `A_a / √α_a` becomes a partial isometry), then extend to a full unitary on `ℂⁿ` via Gram-Schmidt. **The single axiom remaining in the codebase.** Mechanising this is roughly 500-1000 lines of new Lean involving orthogonal projection, partial isometry extension, and projective unitary gauge.
   * *Used by:* the bridge between collinear-feasibility and unitary-collinear factorisations in `GroupIsotope.lean`.

**Status summary:** The codebase has ZERO open-conjecture commitments and ZERO classical-textbook axioms. The only remaining axiom is a manuscript-internal claim from the authors' own Appendix E. All algebraic, spectral, and structural claims are mechanised end-to-end from elementary Mathlib infrastructure.

**Tier 2A complete:** Both sides of the matrix AM-GM lemma AND Schur triangulation are now mechanised end-to-end. The previous axioms `matrix_amgm_at_one`, `matrix_amgm_at_one_equality`, and `matrix_unitary_schur_form` have all been **discharged** as proved theorems. The combined proof is roughly 1000 lines across `Spectral.lean`, `BlockCyclic.lean`, and `MatrixAMGM.lean`. The Schur proof uses the standard induction-on-dimension via Mathlib's `Module.End.exists_eigenvalue` and `Orthonormal.exists_orthonormalBasis_extension_of_card_eq`.

## Scope of Formalization (What is not Mechanized)

This Lean 4 repository focuses strictly on the **algebraic and geometric** properties of the HyperCube model (Sections 3, 4, and parts of 5). It successfully mechanizes the orthogonal decomposition of the objective, collinear identities, normalized rank, and group isotope equivalences. 

**Update:** Tier 3A (continuous optimization existence) and substantial portions of Tier 3B (gauge structure) are now mechanised. See `Tikhonov.lean` and `Coercivity.lean`. The following remains outside scope:

* **Hessian eigenvalue analysis (Appendix F.2):** The Laplacian Hessian's spectral gap controls local coercivity; the explicit eigenvalue analysis is not mechanised.
* **Empirical Pareto frontier (Section 5.3, Figure 2):** The observed `B ≥ 1 − cR` with `c ≈ 0.28` is empirical, not a Lean theorem.

What IS mechanised in `Coercivity.lean` (~3700 lines):
* Per-slot scaling action (`gaugeAction`), unitary conjugation (`unitaryConjAction`), combined action (`combinedGauge`); group structure (composition, inversion, bijectivity); commutativity.
* All optimisation invariants gauge-invariant: `objective`, `hcNormSq`, `kappaTriple`, `inversePenalty`, `misalignPenalty`, `Nondegenerate`, `Factorizes`, `PerfectCollinearity`, `UnitaryCollinear`.
* `LinearMap`, `LinearEquiv`, `ContinuousLinearMap`, `ContinuousLinearEquiv` packagings of each gauge action.
* Combined orbit + setoid + quotient + lifted functions/predicates (`CombinedGaugeQuotient`, `FeasibleCombinedGaugeQuotient`).
* AM-GM bound `H ≥ 3n²` and optimal value `H = 3n²` at UnitaryCollinear classes, both stated at the gauge quotient.

What IS mechanised in `Tikhonov.lean` (~600 lines):
* `HCParams n` topology via product equiv; full `NormedAddCommGroup`, `NormedSpace ℂ`, `FiniteDimensional ℂ` structure.
* Continuity of `objective`, `hcProduct`, `hcNormSq`, slot products.
* Closedness of feasible set; compactness of feasible ∩ closed ball (Heine-Borel).
* Seven existence theorems: minimum on compact feasible, on bounded feasible ball, full Tikhonov-regularised, coercive case, maximum on compact, boundedness on compact, boundedness on bounded ball.

## Admitted Lemmas (`sorry`s)

**None.** The repository contains zero `sorry` statements. Every theorem either has a complete proof or is derived from one of the three explicit `axiom` declarations listed above (all textbook facts).

## Mathlib upstream candidates

The codebase contains several pieces of independent interest to the broader Lean / Mathlib community that would naturally live upstream. **All listed items are now mechanised in this codebase as proved theorems**; upstreaming would primarily involve adapting them to Mathlib's naming conventions and integrating with existing infrastructure.

1. **Unitary Schur triangulation** as a stand-alone theorem `∃ U unitary, U†·A·U is upper triangular for any complex A`. Currently absent in Mathlib (a `TODO` comment in `Mathlib/LinearAlgebra/Eigenspace/Triangularizable.lean` notes this). **Mechanised in `Spectral.lean`** as `matrix_unitary_schur_form` (and `matrix_unitary_schur_form_succ`, `matrix_unitary_schur_form_proved`). Roughly 350 lines, including the inductive step using `Module.End.exists_eigenvalue` and `Orthonormal.exists_orthonormalBasis_extension_of_card_eq`.

2. **Schur trace bound** `‖Tr(T³)‖⁴ ≤ N·(‖T·T‖²_F)³` for upper triangular `T`. Mechanised in `Spectral.lean` as `IsUpperTriangular.norm_trace_cubed_pow_four_le`. Composes triangle inequality, iterated Cauchy-Schwarz, and Schur tightness. Roughly 100 lines.

3. **Matrix AM-GM lemma** `‖XY‖²_F + ‖YZ‖²_F + ‖ZX‖²_F ≥ 3·|τ_n(XYZ)|^{4/3}` (Prof Jeong's appendix). Mechanised in `MatrixAMGM.lean` as `matrix_amgm_at_one`. Builds on Schur trace bound + block-cyclic matrix construction.

4. **Equality rigidity for matrix AM-GM**: at unit normalised trace, equality forces `X, Y, Z` unitary and `XYZ = I`. Mechanised in `MatrixAMGM.lean` as `matrix_amgm_at_one_equality`. Uses three equality cases (triangle, iterated CS, Schur tightness) plus the diagonal-of-cube-roots structural lemma.

5. **Trace-triangle inequality** for upper triangular `T`: `‖Tr(T³)‖ ≤ Σ ‖T_{ii}‖³`. Mechanised as `IsUpperTriangular.norm_trace_cubed_le`.

6. **`(T·T·T)_{ii} = T_{ii}³`** for upper triangular `T`. Mechanised as `IsUpperTriangular.diag_mul_self_mul_self`.

7. **Power-mean Hölder bound** `(Σ f_i³)⁴ ≤ N · (Σ f_i⁴)³` for nonneg real `f`. Mechanised as `Real.sum_pow_three_pow_four_le` via two applications of `Finset.sum_mul_sq_le_sq_mul_sq` (Cauchy-Schwarz).

8. **Reindex preservation of Frobenius² and trace**: `frobNormSq_F (M.submatrix e e) = frobNormSq_F M` and `(M.submatrix e e).trace = M.trace` for `e : Equiv`. Mechanised as `frobNormSq_F_submatrix_equiv` and `trace_submatrix_equiv`.

9. **`AddCommGroup (Fin n)` from a finite quasigroup with an associative commutative cancellative operation**, the bridge described in `PontryaginBridge.lean`. Useful for any project that defines abelian-group structure via Latin squares or cancellation laws rather than via the standard `AddCommGroup` typeclass. Mechanised as `IsAbelianGroup.toAddCommGroup`.

Anyone interested in upstream contributions: items 1-8 are purely linear-algebraic and would be welcome additions to `Mathlib/LinearAlgebra/Matrix/Spectral.lean` (a new file). Item 9 belongs in `Mathlib/Algebra/Group/Defs.lean` adjacent to the existing `Group` and `AddCommGroup` machinery.

## Roadmap (post-Conjecture-17 work)

After the discharge of the abelian-dominance conjectures, the codebase has zero open-conjecture commitments. The remaining items are mechanical mechanisation of textbook spectral facts and scope extensions:

* **Tier 2A part 1** *(complete)*: discharge `matrix_amgm_at_one`. **DONE** — proved end-to-end from `matrix_unitary_schur_form`.
* **Tier 2A part 2** *(complete)*: discharge `matrix_amgm_at_one_equality`. **DONE** — proved end-to-end via the four equality lemmas (triangle, two Cauchy-Schwarz, Schur tightness) plus the cube-roots-of-unity-pair-nonzero argument and the diagonal-of-cube-roots structural lemma.
* **Tier 2A part 3** *(complete)*: discharge `matrix_unitary_schur_form` itself. **DONE** — proved by induction on dimension via `Module.End.exists_eigenvalue`, orthonormal basis extension, `schurUnitary` matrix construction, `liftBlock` block-diagonal lifting, and final composition.
* **Tier 2B** *(κ=1 case complete; κ<1 remains)*: discharge `collinear_to_unitary_collinear`. Manuscript Theorem 21 / Appendix E.
  * **κ=1 sub-case** *(done)*: `kappa_one_collinear_to_unitary_collinear` in `ActiveSubspaceConstruction.lean` discharges the full conditional theorem. Built from `PerfectCollinearity_rescaleByNorm` (unconditional), `Factorizes_rescaleByNorm_of_kappa_one`, and unitarity of all three rescaled slices via `kappa_one_iff_unitary` + chained collinear identities.
  * **κ<1 sub-case**: still requires the manuscript's coordinated active-subspace argument (active-subspace restriction, scaled isometries, projective unitary gauge transformations). Generic active-subspace machinery (`ActiveSubspaceGeneric.lean`, ~555 lines) is in place; the missing piece is coordinating the orthonormal extension across A, B, C.
* **Tier 3A** *(complete)*: existence of global minimisers via Tikhonov regularisation. Manuscript Section 5.1 / Theorem 14 / Corollary 15. `Tikhonov.lean` (~340 lines) provides:
  * HCParams topology via `equivProd` to a product Pi space; full continuity chain (`continuous_objective`, `continuous_hcProduct`, `continuous_hcNormSq`, plus all matrix product / frobNormSq compositions); closedness of the feasible set and norm-bounded sets.
  * Full normed-finite-dim structure on HCParams: `AddCommGroup`, `Module ℂ`, `NormedAddCommGroup`, `NormedSpace ℂ`, `FiniteDimensional ℂ` — all via `Function.Injective` transports through `equivProd`.
  * `isCompact_feasible_inter_ball`: closed feasible set intersected with closed ball of radius R is compact (finite-dim Heine-Borel via `FiniteDimensional.proper`).
  * **Concrete Weierstrass** `exists_minOn_feasible_ball`: if the feasible set has non-empty intersection with the closed ball of radius R, the objective achieves its minimum on that intersection.
* **Tier 3B**: coercivity bounds and gauge stability from Manuscript Appendix F. The largest remaining piece: Laplacian Hessian, scaling potentials, coefficient graph spectral analysis. Roughly 1500-2500 lines. Best approached as a separate sub-project after Tier 3A.
* **Tier 3C** *(complete)*: bridge Mathlib's `AddChar` to `CharacterBasis`, eliminating the basis hypothesis from `Plancherel.lean`.
  * Step 1 *(done)*: `IsAbelianGroup.toAddCommGroup` constructs the `AddCommGroup (Fin n)` instance from the quasigroup cancellation laws.
  * Step 2 *(free)*: Mathlib provides `AddChar (Fin n) ℂ` once `Fin n` carries the abelian-group structure.
  * Step 3 *(done)*: `HCFin` wrapper escapes the `Add (Fin n)` instance conflict; `HCFin.addChar_normSq_one` and `IsAbelianGroup.addCharToCharacter` lift `AddChar (HCFin hab) ℂ` to `Character f`.
  * Step 4 *(done)*: `IsAbelianGroup.characterBasis` constructs a full `CharacterBasis f` (orthogonality + completeness) via `addChar_pairwise_orthogonality` (using `AddChar.expect_eq_ite`) and `addChar_completeness` (using `AddChar.sum_apply_eq_ite` from Pontryagin duality).
* **Tier 3D**: upstream PRs to Mathlib for items 1-9 in the section above.

## Building

Requires [Lean 4](https://leanprover.github.io/) with [Mathlib](https://github.com/leanprover-community/mathlib4) (v4.29.0-rc6).

```bash
cd lean
lake build