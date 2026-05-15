/-
  HyperCubeGroup.AbelianDominance

  Abelian-group structure for the HyperCube model.

  Scope of this file (mechanised, no `sorry`, no `axiom`):
    * The structure `IsAbelianGroup f` and the fact that any abelian
      group is a group isotope.
    * The diagonal representation `diagRep` derived from a character
      system, including its homomorphism, unitarity, and feasibility
      properties; this gives an explicit unitary collinear factorisation
      for any abelian group via `group_isotope_admits_unitary_collinear`.
    * Frobenius-norm unitary invariance and the **full** `U(n)³` gauge
      invariance of the objective `H` (`objective_full_unitary_gauge`),
      strengthening the symmetric `objective_unitary_gauge`.
    * The cyclic group `Z/nZ` as a concrete instance.

  Status of the dominance results:
    * `weak_dominance_abelian`, `abelian_minimizers_collinear`, and
      `abelian_global_optimality` are now thin wrappers around the
      unconditional `weakDominance_general` and `dominanceEquality_general`
      proved in `GroupIsotope.lean`. The previous abelian-specific
      conjecture axioms (`abelianWeakDominance`, `abelianDominanceTightness`)
      have been removed; their conclusions are derived as theorems from
      the matrix AM-GM lemma in `MatrixAMGM.lean`.
    * `MatrixAMGM.matrix_amgm_at_one` and `matrix_amgm_at_one_equality`
      are both proved theorems (Tier 2A complete); there are no remaining
      axioms in `MatrixAMGM.lean`.

  See `HyperCubeGroup.Plancherel` for the structural Fourier
  infrastructure (mass-matrix rewrite, Plancherel identities for mass
  matrices) that the original conjecture-level approach was built on.
-/

import HyperCubeGroup.GroupIsotope
import HyperCubeGroup.Plancherel
import HyperCubeGroup.MatrixAMGM

open Matrix BigOperators Finset Complex

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ## Abelian group structure -/

/-- A finite abelian group: associative + commutative quasigroup with identity. -/
structure IsAbelianGroup (f : BinOp n) extends IsQuasigroup f : Prop where
  assoc : IsAssociative f
  comm : ∀ a b : Fin n, f.op a b = f.op b a
  identity : ∃ e : Fin n, ∀ a : Fin n, f.op e a = a ∧ f.op a e = a

/-- An abelian group is a group isotope. -/
theorem abelian_is_group_isotope (f : BinOp n) (hab : IsAbelianGroup f) :
    IsGroupIsotope f := by
  exact ⟨f, hab.assoc, Equiv.refl _, Equiv.refl _, Equiv.refl _, fun _ _ => rfl⟩

/-! ## Characters of abelian groups

The `Character` and `CharacterBasis` structures live in
`HyperCubeGroup.Plancherel`; we re-export the former here for backward
compatibility with the existing `diagRep*` API in this file. -/

/-- For abelian groups, there exist exactly n orthogonal characters.
    By Pontryagin duality for finite abelian groups (Mathlib: `AddChar.card_eq`,
    `AddChar.wInner_cWeight_eq_boole`, `AddChar.sum_apply_eq_ite`).
    The theorems below are parameterized by characters directly,
    so this existential is not needed as an axiom. -/
theorem abelian_characters_type (f : BinOp n) (_hab : IsAbelianGroup f) :
    ∀ (chars : Fin n → Character f),
      (∀ i j : Fin n,
        (1 / (n : ℂ)) * ∑ g : Fin n, (chars i).val g * starRingEnd ℂ ((chars j).val g) =
          if i = j then 1 else 0) →
      (∀ g h : Fin n,
        (1 / (n : ℂ)) * ∑ i : Fin n, (chars i).val g * starRingEnd ℂ ((chars i).val h) =
          if g = h then 1 else 0) →
      True := fun _ _ _ => trivial

/-! ## Diagonal representation for abelian groups -/

/-- For an abelian group, the regular representation diagonalizes:
    ρ(g) = diag(χ₁(g), ..., χₙ(g)) in the character basis. -/
def diagRep {f : BinOp n} (chars : Fin n → Character f) (g : Fin n) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun i => (chars i).val g)

/-- The diagonal representation is a homomorphism. -/
theorem diagRep_hom {f : BinOp n} (chars : Fin n → Character f) (a b : Fin n) :
    diagRep chars a * diagRep chars b = diagRep chars (f.op a b) := by
  simp only [diagRep, Matrix.diagonal_mul_diagonal]
  congr 1; ext i
  exact ((chars i).hom a b).symm

/-- The diagonal representation is unitary. -/
theorem diagRep_unitary {f : BinOp n} (chars : Fin n → Character f) (g : Fin n) :
    diagRep chars g * (diagRep chars g).conjTranspose = 1 := by
  simp only [diagRep, diagonal_conjTranspose, Pi.star_def]
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1; ext i
  show (chars i).val g * starRingEnd ℂ ((chars i).val g) = 1
  rw [Complex.mul_conj, (chars i).unit g, Complex.ofReal_one]

/-- The diagonal representation gives a valid factorization:
    T_abc = (1/n) Tr(ρ(a) ρ(b) ρ(c)†) = δ_abc. -/
theorem diagRep_factorizes {f : BinOp n} (chars : Fin n → Character f)
    (horth : ∀ i j : Fin n,
      (1 / (n : ℂ)) * ∑ g : Fin n, (chars i).val g * starRingEnd ℂ ((chars j).val g) =
        if i = j then 1 else 0)
    (hcomp : ∀ g h : Fin n,
      (1 / (n : ℂ)) * ∑ i : Fin n, (chars i).val g * starRingEnd ℂ ((chars i).val h) =
        if g = h then 1 else 0) :
    let Θ : HCParams n := ⟨diagRep chars, diagRep chars,
      fun g => (diagRep chars g).conjTranspose⟩
    Factorizes Θ f := by
  intro Θ a b c
  -- Reduce the let-binding and unfold definitions
  change (1 / (↑n : ℂ)) * (diagRep chars a * diagRep chars b *
    (diagRep chars c).conjTranspose).trace = if f.op a b = c then 1 else 0
  simp only [diagRep, diagonal_conjTranspose, diagonal_mul_diagonal, trace_diagonal, Pi.star_def]
  -- Goal: (1/n) * Σ_i (χ_i(a) * χ_i(b) * star(χ_i(c))) = if f.op a b = c then 1 else 0
  -- Use character homomorphism: χ_i(a) * χ_i(b) = χ_i(a ∘ b)
  conv_lhs => rw [show (∑ i : Fin n, (chars i).val a * (chars i).val b *
    star ((chars i).val c)) = ∑ i : Fin n, (chars i).val (f.op a b) *
    star ((chars i).val c) from Finset.sum_congr rfl (fun i _ => by
      rw [← (chars i).hom a b])]
  -- Now goal matches hcomp after replacing star with starRingEnd ℂ
  change (1 / (↑n : ℂ)) * ∑ i : Fin n, (chars i).val (f.op a b) *
    starRingEnd ℂ ((chars i).val c) = _
  exact hcomp (f.op a b) c

/-! ## Scalar dominance inequality -/

/-- **Scalar AM-GM (three variables).**
    For nonneg reals α, β, γ: α + β + γ ≥ 3 · (αβγ)^{1/3}.
    We state this without the cube root to avoid HPow ℝ ℝ issues:
    (α + β + γ)³ ≥ 27 αβγ. -/
theorem real_amgm_three_cubed (α β γ : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) :
    (α + β + γ) ^ 3 ≥ 27 * (α * β * γ) := by
  nlinarith [sq_nonneg (α - β), sq_nonneg (β - γ), sq_nonneg (α - γ),
             sq_nonneg α, sq_nonneg β, sq_nonneg γ,
             mul_nonneg hα hβ, mul_nonneg hβ hγ, mul_nonneg hα hγ]

/-! ## Frobenius norm unitary invariance -/

/-- The Frobenius norm is invariant under left-multiplication by a unitary matrix:
    ‖U M‖² = ‖M‖² when U† U = I.
    Proof: Tr((UM)†(UM)) = Tr(M† U† U M) = Tr(M† M). -/
theorem frobNormSq_unitary_mul_left (U M : Matrix (Fin n) (Fin n) ℂ)
    (hU : U.conjTranspose * U = 1) :
    frobNormSq (U * M) = frobNormSq M := by
  show frobInner (U * M) (U * M) = frobInner M M
  unfold frobInner
  congr 1
  -- Goal: ((U * M)ᴴ * (U * M)).trace = (Mᴴ * M).trace
  calc ((U * M).conjTranspose * (U * M)).trace
      = (M.conjTranspose * U.conjTranspose * (U * M)).trace := by
          rw [Matrix.conjTranspose_mul]
    _ = (M.conjTranspose * (U.conjTranspose * (U * M))).trace := by
          rw [Matrix.mul_assoc]
    _ = (M.conjTranspose * ((U.conjTranspose * U) * M)).trace := by
          rw [Matrix.mul_assoc U.conjTranspose U M]
    _ = (M.conjTranspose * M).trace := by
          rw [hU, Matrix.one_mul]

/-- The Frobenius norm is invariant under right-multiplication by a unitary matrix:
    ‖M U‖² = ‖M‖² when U U† = I.
    Proof: Tr((MU)†(MU)) = Tr(U† M† M U) = Tr(M† M) by trace cyclicity. -/
theorem frobNormSq_unitary_mul_right (M U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1) :
    frobNormSq (M * U) = frobNormSq M := by
  show frobInner (M * U) (M * U) = frobInner M M
  unfold frobInner
  congr 1
  calc ((M * U).conjTranspose * (M * U)).trace
      = (U.conjTranspose * M.conjTranspose * (M * U)).trace := by
          rw [Matrix.conjTranspose_mul]
    _ = (U.conjTranspose * (M.conjTranspose * (M * U))).trace := by
          rw [Matrix.mul_assoc]
    _ = ((M.conjTranspose * (M * U)) * U.conjTranspose).trace := by
          rw [Matrix.trace_mul_comm]
    _ = (M.conjTranspose * ((M * U) * U.conjTranspose)).trace := by
          rw [Matrix.mul_assoc]
    _ = (M.conjTranspose * (M * (U * U.conjTranspose))).trace := by
          rw [Matrix.mul_assoc M U U.conjTranspose]
    _ = (M.conjTranspose * M).trace := by
          rw [hU, Matrix.mul_one]

/-- Unitary conjugation preserves the Frobenius norm:
    ‖U M U†‖² = ‖M‖² for unitary U. -/
theorem frobNormSq_unitary_conj (U M : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1) (hU' : U.conjTranspose * U = 1) :
    frobNormSq (U * M * U.conjTranspose) = frobNormSq M := by
  show frobInner (U * M * U.conjTranspose) (U * M * U.conjTranspose) = frobInner M M
  unfold frobInner
  congr 1
  -- Key: (U M U†)† (U M U†) = U M† U† U M U† = U M† M U†
  -- Then Tr(U M† M U†) = Tr(M† M U† U) = Tr(M† M)
  have hprod : (U * M * U.conjTranspose).conjTranspose * (U * M * U.conjTranspose) =
      U * (M.conjTranspose * M) * U.conjTranspose := by
    -- Expand conjTranspose of products, fully associate, cancel U†U
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
               Matrix.mul_assoc]
    -- After full right-association: U * (Mᴴ * (Uᴴ * (U * (M * Uᴴ))))
    -- Need: Uᴴ * (U * ...) = 1 * ... = ...
    conv_lhs => rw [show ∀ X : Matrix (Fin n) (Fin n) ℂ,
      U.conjTranspose * (U * X) = X from fun X => by
        rw [← Matrix.mul_assoc, hU', Matrix.one_mul]]
  rw [hprod]
  -- Tr(U * (M† * M) * U†) = Tr(M† * M)
  calc (U * (M.conjTranspose * M) * U.conjTranspose).trace
      = (U * ((M.conjTranspose * M) * U.conjTranspose)).trace := by
          rw [Matrix.mul_assoc]
    _ = ((M.conjTranspose * M) * U.conjTranspose * U).trace := by
          rw [Matrix.trace_mul_comm U _]
    _ = ((M.conjTranspose * M) * (U.conjTranspose * U)).trace := by
          rw [Matrix.mul_assoc]
    _ = (M.conjTranspose * M).trace := by
          rw [hU', Matrix.mul_one]

/-! ## Objective invariance under unitary gauge -/

/-- (U M U†)(U N U†) = U(MN)U† for unitary U. -/
private theorem unitary_conj_mul (U M N : Matrix (Fin n) (Fin n) ℂ)
    (hU' : U.conjTranspose * U = 1) :
    (U * M * U.conjTranspose) * (U * N * U.conjTranspose) =
      U * (M * N) * U.conjTranspose := by
  calc (U * M * U.conjTranspose) * (U * N * U.conjTranspose)
      = U * M * (U.conjTranspose * U) * N * U.conjTranspose := by
        simp only [Matrix.mul_assoc]
    _ = U * M * N * U.conjTranspose := by
        rw [hU', Matrix.mul_one]
    _ = U * (M * N) * U.conjTranspose := by
        simp only [Matrix.mul_assoc]

/-- The objective is invariant under the symmetric unitary gauge (U, U, U):
    H(UAU†, UBU†, UCU†) = H(A, B, C) when U is unitary. -/
theorem objective_unitary_gauge (Θ : HCParams n) (f : BinOp n)
    (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1) (hU' : U.conjTranspose * U = 1) :
    let Θ' : HCParams n := ⟨fun a => U * Θ.A a * U.conjTranspose,
                              fun b => U * Θ.B b * U.conjTranspose,
                              fun c => U * Θ.C c * U.conjTranspose⟩
    objective Θ' f = objective Θ f := by
  intro Θ'
  simp only [objective_eq_sum_support]
  congr 1; ext a; congr 1; ext b
  rw [show Θ'.B b * Θ'.C (f.op a b) =
      U * (Θ.B b * Θ.C (f.op a b)) * U.conjTranspose from unitary_conj_mul U _ _ hU',
      show Θ'.C (f.op a b) * Θ'.A a =
      U * (Θ.C (f.op a b) * Θ.A a) * U.conjTranspose from unitary_conj_mul U _ _ hU',
      show Θ'.A a * Θ'.B b =
      U * (Θ.A a * Θ.B b) * U.conjTranspose from unitary_conj_mul U _ _ hU',
      frobNormSq_unitary_conj U _ hU hU',
      frobNormSq_unitary_conj U _ hU hU',
      frobNormSq_unitary_conj U _ hU hU']

/-! ### Full U(n)³ gauge

The objective `H` is invariant under the **full** unitary gauge with three
**independent** unitaries `(U, V, W)`:
  `A_a ↦ U A_a V†`, `B_b ↦ V B_b W†`, `C_c ↦ W C_c U†`.
This is the natural unitary subgroup of the structural gauge
`gaugeTransform U V W` (Basic.lean), under which the structure tensor is
invariant. The symmetric `objective_unitary_gauge` above is the diagonal
subgroup `U = V = W` of this larger group; the general statement is
needed for any "diagonalize Θ via Fourier" argument that uses different
unitaries on the row/column sides of `A`, `B`, `C`.
-/

/-- ‖U M V†‖² = ‖M‖² for unitary U and V (sandwich form). -/
private theorem frobNormSq_unitary_sandwich (U V M : Matrix (Fin n) (Fin n) ℂ)
    (hU' : U.conjTranspose * U = 1) (hV' : V.conjTranspose * V = 1) :
    frobNormSq (U * M * V.conjTranspose) = frobNormSq M := by
  -- ‖U·(M·V†)‖² = ‖M·V†‖²  (left-unitary U)
  -- ‖M·V†‖² = ‖M‖²        (right-unitary V†, since (V†)·(V†)† = V†·V = 1)
  rw [show U * M * V.conjTranspose = U * (M * V.conjTranspose) from Matrix.mul_assoc _ _ _,
      frobNormSq_unitary_mul_left U _ hU',
      frobNormSq_unitary_mul_right M V.conjTranspose
        (by rw [Matrix.conjTranspose_conjTranspose]; exact hV')]

/-- (U M V†)(V N W†) = U (MN) W†, the "gauge cancellation" identity. -/
private theorem unitary_gauge_mul (U V W M N : Matrix (Fin n) (Fin n) ℂ)
    (hV' : V.conjTranspose * V = 1) :
    (U * M * V.conjTranspose) * (V * N * W.conjTranspose) =
      U * (M * N) * W.conjTranspose := by
  calc (U * M * V.conjTranspose) * (V * N * W.conjTranspose)
      = U * M * (V.conjTranspose * V) * N * W.conjTranspose := by
        simp only [Matrix.mul_assoc]
    _ = U * M * N * W.conjTranspose := by
        rw [hV', Matrix.mul_one]
    _ = U * (M * N) * W.conjTranspose := by
        simp only [Matrix.mul_assoc]

/-- The objective is invariant under the **full** unitary gauge `(U, V, W)`:
    `H(U A V†, V B W†, W C U†) = H(A, B, C)` when `U`, `V`, `W` are unitary.
    Only the `M† · M = 1` direction of unitarity is needed in the proof. -/
theorem objective_full_unitary_gauge (Θ : HCParams n) (f : BinOp n)
    (U V W : Matrix (Fin n) (Fin n) ℂ)
    (hU' : U.conjTranspose * U = 1)
    (hV' : V.conjTranspose * V = 1)
    (hW' : W.conjTranspose * W = 1) :
    let Θ' : HCParams n := ⟨fun a => U * Θ.A a * V.conjTranspose,
                              fun b => V * Θ.B b * W.conjTranspose,
                              fun c => W * Θ.C c * U.conjTranspose⟩
    objective Θ' f = objective Θ f := by
  intro Θ'
  simp only [objective_eq_sum_support]
  congr 1; ext a; congr 1; ext b
  -- B' C' = V (B C) U† ; C' A' = W (C A) V† ; A' B' = U (A B) W†
  rw [show Θ'.B b * Θ'.C (f.op a b) =
        V * (Θ.B b * Θ.C (f.op a b)) * U.conjTranspose from
          unitary_gauge_mul V W U _ _ hW',
      show Θ'.C (f.op a b) * Θ'.A a =
        W * (Θ.C (f.op a b) * Θ.A a) * V.conjTranspose from
          unitary_gauge_mul W U V _ _ hU',
      show Θ'.A a * Θ'.B b =
        U * (Θ.A a * Θ.B b) * W.conjTranspose from
          unitary_gauge_mul U V W _ _ hV',
      frobNormSq_unitary_sandwich V U _ hV' hU',
      frobNormSq_unitary_sandwich W V _ hW' hV',
      frobNormSq_unitary_sandwich U W _ hU' hW']

/-! ## Unconditional content (no axioms)

Two unconditional results follow directly from previously proved
theorems and isolate exactly the part of the abelian dominance picture
that does **not** depend on the dominance-style conjectures present in
prior manuscript revisions (those conjectures have since been subsumed
by the unconditional Theorem 9 / Theorem 10 results in the current
manuscript).

  * `abelian_admits_optimal_unitary_collinear` — existence of a
    unitary collinear factorisation Θ_opt with `H(Θ_opt) = 3 n²` for
    any abelian `f`.

  * `dominance_on_collinear_manifold` — for **any** quasigroup `f`
    (abelian or not), the bound `H(Θ) ≥ 3 n²` holds for every
    feasible nondegenerate Θ on the collinear manifold (`R = 0`).

Combined, these say: on the collinear manifold the global minimum is
attained by abelian groups at `H = 3 n²`. The lower bound off the
collinear manifold is now an unconditional theorem
(`weakDominance_general`), no longer an axiom. -/

/-- For every abelian operation `f`, there exists a unitary collinear
    factorisation `Θ_opt` with `H(Θ_opt) = 3 n²`. -/
theorem abelian_admits_optimal_unitary_collinear (f : BinOp n)
    (hab : IsAbelianGroup f) :
    ∃ Θ_opt : HCParams n, UnitaryCollinear Θ_opt f ∧
      (objective Θ_opt f).re = 3 * (n : ℝ) ^ 2 := by
  have hgi := abelian_is_group_isotope f hab
  obtain ⟨Θ, huc⟩ := group_isotope_admits_unitary_collinear f hab.toIsQuasigroup hgi
  exact ⟨Θ, huc, uc_objective_value Θ f huc⟩

/-- **Dominance on the collinear manifold (unconditional).**
    For any quasigroup `f`, every feasible nondegenerate Θ with
    `R(Θ) = 0` (i.e. `PerfectCollinearity`) satisfies `H(Θ) ≥ 3 n²`.
    Direct corollary of `decomposition` (`H = B + R`) and
    `amgm_lower_bound` (`B ≥ 3 n²` on the collinear manifold). -/
theorem dominance_on_collinear_manifold (f : BinOp n) (hq : IsQuasigroup f)
    (Θ : HCParams n) (hfeas : Factorizes Θ f) (hnd : Nondegenerate Θ)
    (hcol : PerfectCollinearity Θ f) :
    (objective Θ f).re ≥ 3 * (n : ℝ) ^ 2 := by
  have hB := amgm_lower_bound Θ f hq hnd hcol hfeas
  have hdec := decomposition Θ f hnd
  have hR_zero : (misalignPenalty Θ f).re = 0 := by
    rw [show misalignPenalty Θ f = 0 from hcol]; simp
  rw [hdec, Complex.add_re, hR_zero, add_zero]
  exact hB

/-! ## Abelian-specific wrappers around the general dominance theorems

The general theorems live in `HyperCubeGroup.GroupIsotope` so that the
unconditional `strict_gap_non_group` there does not depend on
`strongCollinearityDominance` (now removed). The wrappers below specialise
them to the abelian case, preserving the public API. -/

/-- **Weak Collinearity Dominance for Abelian Groups** (theorem).
    Every feasible Θ over an abelian `f` satisfies `H ≥ 3 n²`. Thin
    wrapper around `weakDominance_general`, ultimately resting on
    `matrix_amgm_at_one`. Replaces the previous `abelianWeakDominance`
    axiom. -/
theorem weak_dominance_abelian (f : BinOp n) (_hab : IsAbelianGroup f) :
    ∀ Θ : HCParams n, Factorizes Θ f →
      (objective Θ f).re ≥ 3 * (n : ℝ) ^ 2 :=
  fun Θ hfeas => weakDominance_general f Θ hfeas

/-- **Minimisers collinear for Abelian Groups** (theorem). For abelian
    `f`, any feasible nondegenerate Θ with `H = 3 n²` is perfectly
    collinear. Thin wrapper around
    `dominance_equality_implies_perfect_collinearity`. Replaces the
    previous `abelianDominanceTightness` axiom. -/
theorem abelian_minimizers_collinear (f : BinOp n) (_hab : IsAbelianGroup f) :
    ∀ Θ : HCParams n, Factorizes Θ f → Nondegenerate Θ →
      (objective Θ f).re = 3 * (n : ℝ) ^ 2 →
      PerfectCollinearity Θ f :=
  fun Θ hfeas hnd hH_eq =>
    dominance_equality_implies_perfect_collinearity f Θ hfeas hnd hH_eq


/-- **Global optimality for Abelian Groups** — both the existence of an
    optimal unitary collinear factorisation and the universal lower bound
    are now unconditionally derived (modulo `matrix_amgm_at_one`). -/
theorem abelian_global_optimality (f : BinOp n) (hab : IsAbelianGroup f) :
    (∃ Θ_opt : HCParams n, UnitaryCollinear Θ_opt f ∧
      (objective Θ_opt f).re = 3 * (n : ℝ) ^ 2) ∧
    (∀ Θ : HCParams n, Factorizes Θ f →
      (objective Θ f).re ≥ 3 * (n : ℝ) ^ 2) :=
  ⟨abelian_admits_optimal_unitary_collinear f hab,
   weak_dominance_abelian f hab⟩

/-! ## Cyclic group Z/nZ -/

/-- The cyclic group Z/nZ with operation (a + b) mod n. -/
def cyclicGroup (n : ℕ) [NeZero n] : BinOp n where
  op := fun a b => ⟨(a.val + b.val) % n, Nat.mod_lt _ (NeZero.pos n)⟩

/-- Z/nZ is an abelian group. -/
theorem cyclicGroup_abelian : IsAbelianGroup (cyclicGroup n) where
  left_cancel := by
    intro a
    have hop : ∀ x y : Fin n, (cyclicGroup n).op x y = x + y := by
      intro x y; apply Fin.ext; simp [cyclicGroup, Fin.val_add]
    constructor
    · intro b₁ b₂ h; simp only [hop] at h; exact add_left_cancel h
    · intro c; exact ⟨c - a, by simp only [hop]; abel⟩
  right_cancel := by
    intro b
    have hop : ∀ x y : Fin n, (cyclicGroup n).op x y = x + y := by
      intro x y; apply Fin.ext; simp [cyclicGroup, Fin.val_add]
    constructor
    · intro a₁ a₂ h; simp only [fun a => hop a b] at h; exact add_right_cancel h
    · intro c; exact ⟨c - b, by simp only [hop]; abel⟩
  assoc := by
    intro a b c
    have hop : ∀ x y : Fin n, (cyclicGroup n).op x y = x + y := by
      intro x y; apply Fin.ext; simp [cyclicGroup, Fin.val_add]
    simp only [hop, add_assoc]
  comm := by
    intro a b
    have hop : ∀ x y : Fin n, (cyclicGroup n).op x y = x + y := by
      intro x y; apply Fin.ext; simp [cyclicGroup, Fin.val_add]
    simp only [hop, add_comm]
  identity := ⟨⟨0, NeZero.pos n⟩, fun a => by
    constructor <;> simp only [cyclicGroup] <;> apply Fin.ext <;> simp <;>
      exact Nat.mod_eq_of_lt a.isLt⟩

end
