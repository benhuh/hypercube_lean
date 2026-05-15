/-
  HyperCubeGroup.ActiveSubspace

  Active-subspace machinery for the discharge of `collinear_to_unitary_collinear`
  (manuscript Theorem 5, `thm:rigidity` / Appendix C `app:collinearity_rigidity`).

  The construction:
    1. Given a collinear feasible nondegenerate `Θ` for `f`, the
       shared Gram matrix `X = (1/α_a) (Θ.A a) (Θ.A a)ᴴ` is constant
       in `a`, PSD, with `Tr(X) = n`.
    2. Each slice `Θ.A a` satisfies `(Θ.A a) (Θ.A a)ᴴ = α_a · X`.
    3. After rescaling: `(Θ.A a / √α_a) (Θ.A a / √α_a)ᴴ = X`.
    4. By the spectral theorem, `X = U_X · D · U_Xᴴ` with `U_X` unitary
       and `D = diag(λ_1, ..., λ_n)` real nonneg. The "active subspace"
       corresponds to the eigenvalues `λ_i > 0`.
    5. Within the active subspace, `Θ.A a / √α_a` is unitary up to
       a partial isometry. We extend it to a full unitary on `ℂⁿ`
       by orthonormal completion on the orthogonal complement.

  This file mechanises the following layers:

    * `gramA_isHermitian`, `gramA_posSemidef`, `gramA_eigenvalues_nonneg`,
      `gramA_eigenvalues_sum`: Hermitian, PSD, eigenvalues ≥ 0 summing to n.
    * `gramA_mulVec_eigenvector`: gramA · b_i = σ_i · b_i.
    * `A_self_mul_conjTranspose_eigenvector`: A · Aᴴ · b_i = (α σ_i) · b_i.
    * `conjTranspose_eigenvector_of_zero`: σ_i = 0 ⟹ Aᴴ · b_i = 0
      (annihilation of inactive eigenvectors).
    * `normSq_conjTranspose_mulVec_eigenvector`: ‖Aᴴ b_i‖² = α σ_i.
    * `gramA_eigenvector_dotProduct_self`: star b_i ⬝ᵥ b_i = 1
      (unit norm of the eigenvector basis).
    * `gramA_eigenvector_dotProduct_of_ne`: distinct eigenvectors orthogonal.
    * `conjTranspose_mulVec_eigenvector_dotProduct_of_ne`: distinct
      Aᴴ b_i and Aᴴ b_j are orthogonal.
    * `activeNorm Θ a i := √(α σ_i)`, `activeRescaledVec Θ a i :=
      (1/activeNorm) · Aᴴ b_i`.
    * `activeRescaledVec_dotProduct_self`, `activeRescaledVec_dotProduct_of_ne`:
      orthonormality of the active rescaled vectors.
    * `orthonormal_activeRescaledLp_restrict`: in `EuclideanSpace ℂ (Fin n)`,
      the restriction to the active set is orthonormal.
    * `exists_extended_orthonormalBasis`: there exists a full ONB
      indexed by `Fin n` extending the active vectors.
    * `extendedBasis`, `extendedBasis_apply_active`: the chosen extension
      via `Classical.choose`.
    * `activeUnitary` (Q_a): the unitary matrix with columns equal to
      the extended basis vectors.
    * `activeUnitary_mul_conjTranspose`, `activeUnitary_conjTranspose_mul`:
      `Q_a · Q_aᴴ = 1` and `Q_aᴴ · Q_a = 1`.
    * `conjTranspose_mulVec_eigenvector_eq`: **structural identity**
      `Aᴴ · b_j = activeNorm_j · column_j(Q_a)`.
    * `conjTranspose_mul_eigenvectorUnitary_eq`: matrix-form structural
      identity `Aᴴ · U_X = Q_a · diag(activeNorm)`.
    * `A_eq_eigenvectorUnitary_diag_conjTranspose`: **polar form**
      `A_a = U_X · diag(activeNorm) · Q_aᴴ`.
    * `A_mul_activeUnitary_eq`: `A_a · Q_a = U_X · diag(activeNorm)`.
    * `liftedUnitary` (U_X · Q_aᴴ): unitary candidate for `Θ'.A a`.

  **Remaining for the full discharge of `collinear_to_unitary_collinear`:**
    * Analogous machinery for B and C (via gramB, gramC, with the
      appropriate orderings: gramB uses B Bᴴ, but the C-side shared Gram
      uses Cᴴ · C, so the C construction needs a slight adaptation).
    * Construction of `Θ' : HCParams n` from `Q_a, Q_b, Q_c`.
    * Verification of `Factorizes Θ' f` (trace product analysis using
      the polar form for each of A, B, C).
    * Verification of `PerfectCollinearity Θ' f` (collinear identities
      transport through the unitary construction).
-/

import HyperCubeGroup.Spectral
import HyperCubeGroup.CollinearManifold
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Complex.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef

open Matrix BigOperators Complex
open scoped ComplexOrder

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ## Partial isometry: a matrix `V` with `V Vᴴ V = V` -/

/-- A matrix `V` is a partial isometry if `V * Vᴴ * V = V`. Equivalently,
    `V Vᴴ` is the orthogonal projection onto the range of `V`. -/
def Matrix.IsPartialIsometry (V : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  V * Vᴴ * V = V

/-- Every unitary is a partial isometry. -/
theorem Matrix.IsPartialIsometry.of_unitary {V : Matrix (Fin n) (Fin n) ℂ}
    (h : V * Vᴴ = 1) : V.IsPartialIsometry := by
  show V * Vᴴ * V = V
  rw [h, Matrix.one_mul]

/-! ## Hermitian and PSD properties of the shared Gram matrix -/

/-- The shared Gram matrix `gramA Θ a` is Hermitian (since
    `(A Aᴴ)ᴴ = A Aᴴ` for any `A`). -/
theorem gramA_isHermitian (Θ : HCParams n) (a : Fin n) :
    (gramA Θ a).IsHermitian := by
  unfold gramA
  show ((1 / frobNormSq (Θ.A a)) • (Θ.A a * (Θ.A a)ᴴ))ᴴ =
       (1 / frobNormSq (Θ.A a)) • (Θ.A a * (Θ.A a)ᴴ)
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  congr 1
  rw [star_div₀, star_one]
  exact congrArg (1 / ·) (star_frobNormSq _)

/-- `frobNormSq A` is real-valued: equal to its real-coercion. -/
theorem frobNormSq_eq_re_complex (A : Matrix (Fin n) (Fin n) ℂ) :
    frobNormSq A = ((frobNormSq A).re : ℂ) := by
  apply Complex.ext
  · simp
  · simp [frobNormSq_real]

/-- Trace of `gramA Θ a` equals `n`. -/
theorem trace_gramA (Θ : HCParams n) (a : Fin n)
    (hα_ne : frobNormSq (Θ.A a) ≠ 0) :
    (gramA Θ a).trace = (n : ℂ) := by
  unfold gramA
  rw [Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm,
      show ((Θ.A a)ᴴ * Θ.A a).trace = (n : ℂ) * frobNormSq (Θ.A a) from ?_]
  · field_simp
  · -- frobNormSq A = (1/n) Tr(Aᴴ A), so Tr(Aᴴ A) = n · frobNormSq A.
    unfold frobNormSq frobInner
    have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    field_simp

/-- For a nondegenerate `Θ` with `frobNormSq (Θ.A a) > 0`, the
    reciprocal `1 / frobNormSq (Θ.A a)` is a nonneg complex number
    (in the partial-order sense `0 ≤ z`). -/
theorem one_div_frobNormSq_nonneg (Θ : HCParams n) (a : Fin n)
    (hα_pos : 0 < (frobNormSq (Θ.A a)).re) :
    (0 : ℂ) ≤ 1 / frobNormSq (Θ.A a) := by
  rw [Complex.le_def]
  have him : (frobNormSq (Θ.A a)).im = 0 := frobNormSq_real _
  refine ⟨?_, ?_⟩
  · -- (1/frobNormSq).re ≥ 0.
    rw [show (0 : ℂ).re = 0 from rfl]
    rw [show (1 / frobNormSq (Θ.A a)) = (frobNormSq (Θ.A a))⁻¹ from one_div _]
    rw [Complex.inv_re]
    -- (1/α).re = α.re / normSq α. With α.im = 0: normSq α = α.re^2.
    rw [show Complex.normSq (frobNormSq (Θ.A a)) = (frobNormSq (Θ.A a)).re ^ 2 from ?_]
    · positivity
    · rw [Complex.normSq_apply, him]; ring
  · -- (1/frobNormSq).im = 0.
    rw [show (0 : ℂ).im = 0 from rfl]
    rw [show (1 / frobNormSq (Θ.A a)) = (frobNormSq (Θ.A a))⁻¹ from one_div _]
    rw [Complex.inv_im, him]
    simp

/-- The shared Gram matrix `gramA Θ a` is positive semidefinite. -/
theorem gramA_posSemidef (Θ : HCParams n) (a : Fin n)
    (hα_pos : 0 < (frobNormSq (Θ.A a)).re) :
    Matrix.PosSemidef (gramA Θ a) := by
  show Matrix.PosSemidef ((1 / frobNormSq (Θ.A a)) • (Θ.A a * (Θ.A a)ᴴ))
  apply Matrix.PosSemidef.smul (Matrix.posSemidef_self_mul_conjTranspose _)
  exact one_div_frobNormSq_nonneg Θ a hα_pos

/-- Clean matrix identity: `A · Aᴴ = α · gramA Θ a`. -/
theorem A_mul_conjTranspose_eq_smul_gramA (Θ : HCParams n) (a : Fin n)
    (hα_ne : frobNormSq (Θ.A a) ≠ 0) :
    Θ.A a * (Θ.A a)ᴴ = frobNormSq (Θ.A a) • gramA Θ a := by
  show Θ.A a * (Θ.A a)ᴴ =
      frobNormSq (Θ.A a) • ((1 / frobNormSq (Θ.A a)) • (Θ.A a * (Θ.A a)ᴴ))
  rw [smul_smul,
      show frobNormSq (Θ.A a) * (1 / frobNormSq (Θ.A a)) = 1 from by
        field_simp]
  rw [one_smul]

/-! ## Spectral data: eigenvectors and (nonneg) eigenvalues of `gramA` -/

/-- The eigenvalues of `gramA Θ a` are nonneg (by PSD). -/
theorem gramA_eigenvalues_nonneg (Θ : HCParams n) (a : Fin n)
    (hα_pos : 0 < (frobNormSq (Θ.A a)).re) (i : Fin n) :
    0 ≤ (gramA_isHermitian Θ a).eigenvalues i :=
  Matrix.PosSemidef.eigenvalues_nonneg (gramA_posSemidef Θ a hα_pos) i

/-- Sum of eigenvalues of `gramA Θ a` equals `n`. -/
theorem gramA_eigenvalues_sum (Θ : HCParams n) (a : Fin n)
    (hα_ne : frobNormSq (Θ.A a) ≠ 0) :
    ∑ i : Fin n, ((gramA_isHermitian Θ a).eigenvalues i : ℂ) = (n : ℂ) := by
  have h := (gramA_isHermitian Θ a).trace_eq_sum_eigenvalues
  exact h.symm.trans (trace_gramA Θ a hα_ne)

/-! ## Active subspace structure

For each `Θ.A a` and each eigenvector `b_i` of `gramA`:
  * If `eigenvalue i = 0`: `(Θ.A a)ᴴ · b_i = 0` (the inactive eigenvectors
    are annihilated by `(Θ.A a)ᴴ`).
  * If `eigenvalue i > 0`: `(Θ.A a)ᴴ · b_i` has squared norm
    `α_a · eigenvalue i` (in active subspace, the action is determined). -/

variable {Θ : HCParams n}

/-- The eigenvectors of `gramA Θ a` (as functions `Fin n → ℂ` via the
    `EuclideanSpace.equiv`-like coercion). -/
noncomputable def gramA_eigenvector (Θ : HCParams n) (a i : Fin n) :
    Fin n → ℂ :=
  ((gramA_isHermitian Θ a).eigenvectorBasis i : EuclideanSpace ℂ (Fin n))

/-- The shared Gram action on its own eigenvectors. -/
theorem gramA_mulVec_eigenvector (Θ : HCParams n) (a i : Fin n) :
    (gramA Θ a) *ᵥ (gramA_eigenvector Θ a i) =
    ((gramA_isHermitian Θ a).eigenvalues i : ℂ) • (gramA_eigenvector Θ a i) := by
  exact (gramA_isHermitian Θ a).mulVec_eigenvectorBasis i

/-- `A_a · A_aᴴ` acting on the i-th eigenvector of `gramA Θ a`:
    `(A_a · A_aᴴ) *ᵥ b_i = (α_a · σ_i) • b_i`. -/
theorem A_self_mul_conjTranspose_eigenvector (Θ : HCParams n) (a i : Fin n) :
    (Θ.A a * (Θ.A a)ᴴ) *ᵥ (gramA_eigenvector Θ a i) =
    (frobNormSq (Θ.A a) * ((gramA_isHermitian Θ a).eigenvalues i : ℂ)) •
      (gramA_eigenvector Θ a i) := by
  -- A·Aᴴ = α · gramA, so (A·Aᴴ)·v = α · gramA · v = α · (σ • v) = (α·σ) • v.
  have hg : gramA Θ a = (1 / frobNormSq (Θ.A a)) • (Θ.A a * (Θ.A a)ᴴ) := rfl
  -- Multiply both sides by α: α • gramA = α/α • A·Aᴴ = A·Aᴴ (when α ≠ 0).
  -- Or: A·Aᴴ = α • gramA.
  by_cases hα : frobNormSq (Θ.A a) = 0
  · -- α = 0 case (degenerate): A = 0, both sides are 0.
    have hA_zero : Θ.A a = 0 := (frobNormSq_eq_zero_iff _).mp hα
    rw [hα]
    rw [show Θ.A a * (Θ.A a)ᴴ = 0 from by rw [hA_zero]; simp]
    simp
  · -- α ≠ 0 case: A·Aᴴ = α • gramA.
    have hAA : Θ.A a * (Θ.A a)ᴴ = frobNormSq (Θ.A a) • gramA Θ a := by
      rw [hg, smul_smul]
      rw [show frobNormSq (Θ.A a) * (1 / frobNormSq (Θ.A a)) = 1 from by
        field_simp]
      rw [one_smul]
    rw [hAA, Matrix.smul_mulVec, gramA_mulVec_eigenvector, smul_smul]

/-- For inactive eigenvectors (`σ_i = 0`), `A_a · A_aᴴ` annihilates them. -/
theorem A_self_mul_conjTranspose_eigenvector_of_zero
    (Θ : HCParams n) (a i : Fin n)
    (hσ : (gramA_isHermitian Θ a).eigenvalues i = 0) :
    (Θ.A a * (Θ.A a)ᴴ) *ᵥ (gramA_eigenvector Θ a i) = 0 := by
  rw [A_self_mul_conjTranspose_eigenvector Θ a i, hσ]
  simp

/-- For inactive eigenvectors (`σ_i = 0`), `(Θ.A a)ᴴ` annihilates them.

    Proof: `‖Aᴴ b‖² = star(Aᴴ b) ⬝ᵥ (Aᴴ b) = star b ⬝ᵥ A · (Aᴴ b)
    = star b ⬝ᵥ (A · Aᴴ b) = star b ⬝ᵥ 0 = 0` (using
    `A_self_mul_conjTranspose_eigenvector_of_zero`). -/
theorem conjTranspose_eigenvector_of_zero (Θ : HCParams n) (a i : Fin n)
    (hσ : (gramA_isHermitian Θ a).eigenvalues i = 0) :
    (Θ.A a)ᴴ *ᵥ (gramA_eigenvector Θ a i) = 0 := by
  set b := gramA_eigenvector Θ a i with hb_def
  set v := (Θ.A a)ᴴ *ᵥ b with hv_def
  -- Step 1: A · Aᴴ b = 0.
  have hAAH : Θ.A a *ᵥ v = 0 := by
    show Θ.A a *ᵥ ((Θ.A a)ᴴ *ᵥ b) = 0
    rw [Matrix.mulVec_mulVec]
    exact A_self_mul_conjTranspose_eigenvector_of_zero Θ a i hσ
  -- Step 2: Algebraic identity star(v) ⬝ᵥ v = star b ⬝ᵥ A *ᵥ v.
  have hidentity : star v ⬝ᵥ v = star b ⬝ᵥ (Θ.A a *ᵥ v) := by
    -- Using star_mulVec: star v = star ((Θ.A a)ᴴ *ᵥ b) = star b ᵥ* Θ.A a.
    rw [show star v = star b ᵥ* (Θ.A a) from ?_]
    · rw [← Matrix.dotProduct_mulVec]
    · rw [hv_def, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
  -- Step 3: combine.
  have hvv : star v ⬝ᵥ v = 0 := by
    rw [hidentity, hAAH, dotProduct_zero]
  -- Step 4: dotProduct_star_self_eq_zero ⇒ v = 0.
  exact dotProduct_star_self_eq_zero.mp hvv

/-! ## Orthonormality of the eigenvector basis (as star ⬝ᵥ identities) -/

/-- The eigenvectors of `gramA Θ a` are unit vectors:
    `star b_i ⬝ᵥ b_i = 1`. -/
theorem gramA_eigenvector_dotProduct_self (Θ : HCParams n) (a i : Fin n) :
    star (gramA_eigenvector Θ a i) ⬝ᵥ gramA_eigenvector Θ a i = 1 := by
  -- ‖eigenvectorBasis i‖ = 1 ⟹ ⟨b, b⟩ = 1 = ofLp b ⬝ᵥ star (ofLp b) = b ⬝ᵥ star b.
  -- Then dotProduct_comm gives star b ⬝ᵥ b = 1.
  have horth : ‖(gramA_isHermitian Θ a).eigenvectorBasis i‖ = 1 :=
    (gramA_isHermitian Θ a).eigenvectorBasis.orthonormal.1 i
  have hinner :
      @inner ℂ _ _ ((gramA_isHermitian Θ a).eigenvectorBasis i)
        ((gramA_isHermitian Θ a).eigenvectorBasis i) = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, horth]
    simp
  rw [show star (gramA_eigenvector Θ a i) ⬝ᵥ gramA_eigenvector Θ a i =
        gramA_eigenvector Θ a i ⬝ᵥ star (gramA_eigenvector Θ a i)
        from dotProduct_comm _ _]
  rw [show gramA_eigenvector Θ a i ⬝ᵥ star (gramA_eigenvector Θ a i) =
        @inner ℂ _ _ ((gramA_isHermitian Θ a).eigenvectorBasis i)
          ((gramA_isHermitian Θ a).eigenvectorBasis i)
        from (EuclideanSpace.inner_eq_star_dotProduct _ _).symm]
  exact hinner

/-! ## Active subspace norm: `‖Aᴴ b_i‖² = α_a · σ_i` -/

/-- The squared norm of `Aᴴ b_i` (in spectral coordinates) is `α_a · σ_i`. -/
theorem normSq_conjTranspose_mulVec_eigenvector (Θ : HCParams n) (a i : Fin n) :
    star ((Θ.A a)ᴴ *ᵥ gramA_eigenvector Θ a i) ⬝ᵥ
      ((Θ.A a)ᴴ *ᵥ gramA_eigenvector Θ a i) =
    frobNormSq (Θ.A a) * ((gramA_isHermitian Θ a).eigenvalues i : ℂ) := by
  set b := gramA_eigenvector Θ a i with hb_def
  set v := (Θ.A a)ᴴ *ᵥ b with hv_def
  -- star v ⬝ᵥ v = star b ⬝ᵥ (A *ᵥ v) = star b ⬝ᵥ ((α σ) • b) = (α σ) (star b ⬝ᵥ b) = α σ.
  have hAAv : Θ.A a *ᵥ v =
      (frobNormSq (Θ.A a) * ((gramA_isHermitian Θ a).eigenvalues i : ℂ)) • b := by
    show Θ.A a *ᵥ ((Θ.A a)ᴴ *ᵥ b) = _
    rw [Matrix.mulVec_mulVec]
    exact A_self_mul_conjTranspose_eigenvector Θ a i
  have hidentity : star v ⬝ᵥ v = star b ⬝ᵥ (Θ.A a *ᵥ v) := by
    rw [show star v = star b ᵥ* (Θ.A a) from ?_]
    · rw [← Matrix.dotProduct_mulVec]
    · rw [hv_def, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
  rw [hidentity, hAAv, dotProduct_smul, smul_eq_mul,
      gramA_eigenvector_dotProduct_self, mul_one]

/-! ## Orthogonality between distinct eigenvectors -/

/-- Distinct eigenvectors of `gramA Θ a` are orthogonal. -/
theorem gramA_eigenvector_dotProduct_of_ne (Θ : HCParams n) (a i j : Fin n)
    (hij : i ≠ j) :
    star (gramA_eigenvector Θ a i) ⬝ᵥ gramA_eigenvector Θ a j = 0 := by
  -- ⟨b_i, b_j⟩ = 0 by orthonormality.
  have horth :
      @inner ℂ _ _ ((gramA_isHermitian Θ a).eigenvectorBasis i)
        ((gramA_isHermitian Θ a).eigenvectorBasis j) = (0 : ℂ) :=
    (gramA_isHermitian Θ a).eigenvectorBasis.orthonormal.2 hij
  rw [show star (gramA_eigenvector Θ a i) ⬝ᵥ gramA_eigenvector Θ a j =
        gramA_eigenvector Θ a j ⬝ᵥ star (gramA_eigenvector Θ a i)
        from dotProduct_comm _ _]
  rw [show gramA_eigenvector Θ a j ⬝ᵥ star (gramA_eigenvector Θ a i) =
        @inner ℂ _ _ ((gramA_isHermitian Θ a).eigenvectorBasis i)
          ((gramA_isHermitian Θ a).eigenvectorBasis j)
        from (EuclideanSpace.inner_eq_star_dotProduct _ _).symm]
  exact horth

/-- The vectors `Aᴴ b_i` and `Aᴴ b_j` are orthogonal for distinct `i, j`. -/
theorem conjTranspose_mulVec_eigenvector_dotProduct_of_ne
    (Θ : HCParams n) (a i j : Fin n) (hij : i ≠ j) :
    star ((Θ.A a)ᴴ *ᵥ gramA_eigenvector Θ a i) ⬝ᵥ
      ((Θ.A a)ᴴ *ᵥ gramA_eigenvector Θ a j) = 0 := by
  set bi := gramA_eigenvector Θ a i with hbi_def
  set bj := gramA_eigenvector Θ a j with hbj_def
  set vi := (Θ.A a)ᴴ *ᵥ bi with hvi_def
  set vj := (Θ.A a)ᴴ *ᵥ bj with hvj_def
  -- star vi ⬝ᵥ vj = star bi ⬝ᵥ (A *ᵥ vj) = star bi ⬝ᵥ ((α σ_j) • bj)
  -- = (α σ_j) (star bi ⬝ᵥ bj) = (α σ_j) · 0 = 0.
  have hAAvj : Θ.A a *ᵥ vj =
      (frobNormSq (Θ.A a) * ((gramA_isHermitian Θ a).eigenvalues j : ℂ)) • bj := by
    show Θ.A a *ᵥ ((Θ.A a)ᴴ *ᵥ bj) = _
    rw [Matrix.mulVec_mulVec]
    exact A_self_mul_conjTranspose_eigenvector Θ a j
  have hidentity : star vi ⬝ᵥ vj = star bi ⬝ᵥ (Θ.A a *ᵥ vj) := by
    rw [show star vi = star bi ᵥ* (Θ.A a) from ?_]
    · rw [← Matrix.dotProduct_mulVec]
    · rw [hvi_def, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
  rw [hidentity, hAAvj, dotProduct_smul, smul_eq_mul,
      gramA_eigenvector_dotProduct_of_ne Θ a i j hij, mul_zero]

/-! ## Active rescaled vectors `c_i := (1/√(α σ_i)) Aᴴ b_i` -/

/-- The active norm `√(α_a · σ_i)` as a nonneg real number. -/
noncomputable def activeNorm (Θ : HCParams n) (a i : Fin n) : ℝ :=
  Real.sqrt ((frobNormSq (Θ.A a)).re * (gramA_isHermitian Θ a).eigenvalues i)

/-- The rescaled active vector `(1/√(α σ_i)) Aᴴ b_i`.

    For active `i` (where `σ_i > 0`): this is a unit vector.
    For inactive `i` (where `σ_i = 0`): `Aᴴ b_i = 0`, and the formula
    yields `0` as well (since `(0 : ℂ)⁻¹ = 0` in Mathlib). -/
noncomputable def activeRescaledVec (Θ : HCParams n) (a i : Fin n) :
    Fin n → ℂ :=
  ((activeNorm Θ a i : ℂ)⁻¹) • ((Θ.A a)ᴴ *ᵥ gramA_eigenvector Θ a i)

/-- For active eigenvectors (σ_i > 0 and α_a > 0), the rescaled vector
    has unit norm. -/
theorem activeRescaledVec_dotProduct_self
    (Θ : HCParams n) (a i : Fin n)
    (hα_pos : 0 < (frobNormSq (Θ.A a)).re)
    (hσ_pos : 0 < (gramA_isHermitian Θ a).eigenvalues i) :
    star (activeRescaledVec Θ a i) ⬝ᵥ activeRescaledVec Θ a i = 1 := by
  unfold activeRescaledVec
  rw [star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      normSq_conjTranspose_mulVec_eigenvector, frobNormSq_eq_re_complex]
  -- Goal: star ((↑an)⁻¹) * ((↑an)⁻¹ * (↑α * ↑σ)) = 1, where α, σ ∈ ℝ.
  set α := (frobNormSq (Θ.A a)).re with hα_def
  set σ := (gramA_isHermitian Θ a).eigenvalues i with hσ_def
  have hαnn : 0 ≤ α := le_of_lt hα_pos
  have hσnn : 0 ≤ σ := le_of_lt hσ_pos
  -- (activeNorm)² = α σ (both real nonneg).
  have h_an_sq_R : (activeNorm Θ a i)^2 = α * σ := by
    unfold activeNorm; exact Real.sq_sqrt (mul_nonneg hαnn hσnn)
  have h_an_pos : 0 < activeNorm Θ a i := by
    unfold activeNorm; exact Real.sqrt_pos.mpr (mul_pos hα_pos hσ_pos)
  have h_an_ne : (activeNorm Θ a i : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt h_an_pos)
  -- star ((↑an)⁻¹) = (↑an)⁻¹ since an is real.
  have hstar : star ((activeNorm Θ a i : ℂ)⁻¹) = (activeNorm Θ a i : ℂ)⁻¹ := by
    rw [show (activeNorm Θ a i : ℂ)⁻¹ = ((activeNorm Θ a i)⁻¹ : ℂ) from by push_cast; rfl]
    simp
  rw [hstar]
  -- Reduce to showing (an : ℂ)² = ↑α * ↑σ, then field_simp.
  have h_an_sq_C : (activeNorm Θ a i : ℂ) * (activeNorm Θ a i : ℂ) =
      (α : ℂ) * (σ : ℂ) := by
    have : ((activeNorm Θ a i)^2 : ℂ) = ((α * σ : ℝ) : ℂ) := by
      exact_mod_cast h_an_sq_R
    rw [show (activeNorm Θ a i : ℂ) * (activeNorm Θ a i : ℂ) =
          ((activeNorm Θ a i)^2 : ℂ) from by push_cast; ring]
    rw [this]; push_cast; ring
  rw [show ((activeNorm Θ a i : ℂ)⁻¹) * ((activeNorm Θ a i : ℂ)⁻¹ *
        ((α : ℂ) * (σ : ℂ))) =
        ((α : ℂ) * (σ : ℂ)) /
        ((activeNorm Θ a i : ℂ) * (activeNorm Θ a i : ℂ))
        from by field_simp]
  rw [h_an_sq_C, div_self]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hα_pos))
    (Complex.ofReal_ne_zero.mpr (ne_of_gt hσ_pos))

/-- For distinct active eigenvectors, the rescaled vectors are orthogonal. -/
theorem activeRescaledVec_dotProduct_of_ne
    (Θ : HCParams n) (a i j : Fin n) (hij : i ≠ j) :
    star (activeRescaledVec Θ a i) ⬝ᵥ activeRescaledVec Θ a j = 0 := by
  unfold activeRescaledVec
  rw [star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      conjTranspose_mulVec_eigenvector_dotProduct_of_ne Θ a i j hij,
      mul_zero, mul_zero]

/-! ## Orthonormal extension via Mathlib

The active rescaled vectors `{c_i : σ_i > 0}` are orthonormal. By
`Orthonormal.exists_orthonormalBasis_extension_of_card_eq`, this family
extends to a full orthonormal basis indexed by `Fin n` of
`EuclideanSpace ℂ (Fin n)`. -/

/-- The active set: indices `i` for which `σ_i ≠ 0`. -/
def activeSet (Θ : HCParams n) (a : Fin n) : Set (Fin n) :=
  {i | (gramA_isHermitian Θ a).eigenvalues i ≠ 0}

/-- The active rescaled vector lifted to `EuclideanSpace ℂ (Fin n)`. -/
noncomputable def activeRescaledLp (Θ : HCParams n) (a i : Fin n) :
    EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (activeRescaledVec Θ a i)

/-- The lifted vector evaluated at `j` equals the underlying vector at `j`. -/
@[simp] lemma activeRescaledLp_apply (Θ : HCParams n) (a i j : Fin n) :
    activeRescaledLp Θ a i j = activeRescaledVec Θ a i j := rfl

/-- The active rescaled vectors restricted to the active set form an
    orthonormal family in `EuclideanSpace ℂ (Fin n)`, provided
    `α_a > 0`. -/
theorem orthonormal_activeRescaledLp_restrict (Θ : HCParams n) (a : Fin n)
    (hα_pos : 0 < (frobNormSq (Θ.A a)).re) :
    Orthonormal ℂ ((activeSet Θ a).restrict (activeRescaledLp Θ a)) := by
  rw [orthonormal_iff_ite]
  intro ⟨i, hi⟩ ⟨j, hj⟩
  simp only [Set.restrict_apply]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  -- ⟨v_i, v_j⟩ = ofLp v_j ⬝ᵥ star (ofLp v_i) = v_j ⬝ᵥ star v_i = star v_i ⬝ᵥ v_j
  rw [show
      WithLp.ofLp (activeRescaledLp Θ a j) ⬝ᵥ star (WithLp.ofLp (activeRescaledLp Θ a i))
      = star (activeRescaledVec Θ a i) ⬝ᵥ activeRescaledVec Θ a j from by
    rw [show WithLp.ofLp (activeRescaledLp Θ a j) = activeRescaledVec Θ a j from rfl,
        show WithLp.ofLp (activeRescaledLp Θ a i) = activeRescaledVec Θ a i from rfl]
    exact dotProduct_comm _ _]
  by_cases hij : i = j
  · subst hij
    simp only [Subtype.mk.injEq, if_true]
    have hσ_pos : 0 < (gramA_isHermitian Θ a).eigenvalues i := by
      have hσnn := gramA_eigenvalues_nonneg Θ a hα_pos i
      have hσne : (gramA_isHermitian Θ a).eigenvalues i ≠ 0 := hi
      exact lt_of_le_of_ne hσnn (Ne.symm hσne)
    exact activeRescaledVec_dotProduct_self Θ a i hα_pos hσ_pos
  · simp only [Subtype.mk.injEq, hij, if_false]
    exact activeRescaledVec_dotProduct_of_ne Θ a i j hij

/-- **Orthonormal extension theorem (existence).** The active rescaled
    vectors extend to a full orthonormal basis of `EuclideanSpace ℂ (Fin n)`
    indexed by `Fin n`. -/
theorem exists_extended_orthonormalBasis (Θ : HCParams n) (a : Fin n)
    (hα_pos : 0 < (frobNormSq (Θ.A a)).re) :
    ∃ b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)),
      ∀ i ∈ activeSet Θ a, b i = activeRescaledLp Θ a i := by
  have hcard : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = Fintype.card (Fin n) := by
    rw [finrank_euclideanSpace_fin, Fintype.card_fin]
  exact (orthonormal_activeRescaledLp_restrict Θ a hα_pos).exists_orthonormalBasis_extension_of_card_eq hcard

/-! ## Construction of the active unitary `Q_a`

Given the extended orthonormal basis, we get a unitary matrix `Q_a` on
`Fin n × Fin n` with columns equal to the basis vectors. By construction,
the columns indexed by active `i` are `activeRescaledLp Θ a i`, i.e. the
rescaled active rows of `Aᴴ`. -/

/-- The extended orthonormal basis, chosen via `Classical.choose`. -/
noncomputable def extendedBasis (Θ : HCParams n) (a : Fin n)
    (hα_pos : 0 < (frobNormSq (Θ.A a)).re) :
    OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)) :=
  Classical.choose (exists_extended_orthonormalBasis Θ a hα_pos)

/-- The defining property of `extendedBasis`: it agrees with
    `activeRescaledLp` on the active set. -/
theorem extendedBasis_apply_active (Θ : HCParams n) (a : Fin n)
    (hα_pos : 0 < (frobNormSq (Θ.A a)).re)
    (i : Fin n) (hi : i ∈ activeSet Θ a) :
    extendedBasis Θ a hα_pos i = activeRescaledLp Θ a i :=
  Classical.choose_spec (exists_extended_orthonormalBasis Θ a hα_pos) i hi

/-- The active unitary `Q_a`: the unitary matrix whose columns are the
    extended basis vectors. -/
noncomputable def activeUnitary (Θ : HCParams n) (a : Fin n)
    (hα_pos : 0 < (frobNormSq (Θ.A a)).re) :
    Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨(EuclideanSpace.basisFun (Fin n) ℂ).toBasis.toMatrix
      (extendedBasis Θ a hα_pos).toBasis,
   (EuclideanSpace.basisFun (Fin n) ℂ).toMatrix_orthonormalBasis_mem_unitary
      (extendedBasis Θ a hα_pos)⟩

/-- `activeUnitary` is in the unitary group (i.e. `Q_a · Q_aᴴ = 1`). -/
theorem activeUnitary_mul_conjTranspose (Θ : HCParams n) (a : Fin n)
    (hα_pos : 0 < (frobNormSq (Θ.A a)).re) :
    (activeUnitary Θ a hα_pos : Matrix (Fin n) (Fin n) ℂ) *
      (activeUnitary Θ a hα_pos : Matrix (Fin n) (Fin n) ℂ).conjTranspose = 1 :=
  (EuclideanSpace.basisFun (Fin n) ℂ).toMatrix_orthonormalBasis_self_mul_conjTranspose
    (extendedBasis Θ a hα_pos)

/-- `activeUnitary` is in the unitary group (other direction:
    `Q_aᴴ · Q_a = 1`). -/
theorem activeUnitary_conjTranspose_mul (Θ : HCParams n) (a : Fin n)
    (hα_pos : 0 < (frobNormSq (Θ.A a)).re) :
    (activeUnitary Θ a hα_pos : Matrix (Fin n) (Fin n) ℂ).conjTranspose *
      (activeUnitary Θ a hα_pos : Matrix (Fin n) (Fin n) ℂ) = 1 :=
  (EuclideanSpace.basisFun (Fin n) ℂ).toMatrix_orthonormalBasis_conjTranspose_mul_self
    (extendedBasis Θ a hα_pos)

/-! ## Lifted unitary `Θ'.A a := U · Q_aᴴ`

A natural unitary candidate built from the eigenvector unitary `U` (of
`gramA`) and the active unitary `Q_a`. This is the "easy" lift; the full
manuscript construction also requires verifying that it preserves
`Factorizes` and `PerfectCollinearity`. -/

/-- The candidate unitary `U_X · Q_aᴴ` (in original coordinates). -/
noncomputable def liftedUnitary (Θ : HCParams n) (a : Fin n)
    (hα_pos : 0 < (frobNormSq (Θ.A a)).re) :
    Matrix (Fin n) (Fin n) ℂ :=
  ((gramA_isHermitian Θ a).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
    (activeUnitary Θ a hα_pos : Matrix (Fin n) (Fin n) ℂ).conjTranspose

/-- The j-th column of `activeUnitary` equals the j-th extended basis vector. -/
theorem activeUnitary_col (Θ : HCParams n) (a : Fin n)
    (hα_pos : 0 < (frobNormSq (Θ.A a)).re) (i j : Fin n) :
    (activeUnitary Θ a hα_pos : Matrix (Fin n) (Fin n) ℂ) i j =
    (extendedBasis Θ a hα_pos j : EuclideanSpace ℂ (Fin n)) i := rfl

/-- **Key structural identity.** For each eigenvector `b_j` of `gramA`,
    `Aᴴ · b_j = activeNorm_j · (j-th column of Q_a)`. This holds for both
    active `j` (where both sides are nonzero) and inactive `j` (both sides
    are zero, by annihilation and `activeNorm = 0`). -/
theorem conjTranspose_mulVec_eigenvector_eq (Θ : HCParams n) (a j : Fin n)
    (hα_pos : 0 < (frobNormSq (Θ.A a)).re) :
    (Θ.A a)ᴴ *ᵥ gramA_eigenvector Θ a j =
    (activeNorm Θ a j : ℂ) •
      (fun i => (activeUnitary Θ a hα_pos : Matrix (Fin n) (Fin n) ℂ) i j) := by
  by_cases hj : (gramA_isHermitian Θ a).eigenvalues j = 0
  · -- Inactive case: both sides are 0.
    rw [conjTranspose_eigenvector_of_zero Θ a j hj]
    have h_an_zero : activeNorm Θ a j = 0 := by
      unfold activeNorm; rw [hj, mul_zero, Real.sqrt_zero]
    rw [h_an_zero]; simp
  · -- Active case.
    have hj_act : j ∈ activeSet Θ a := hj
    -- column j of activeUnitary is activeRescaledLp j = activeRescaledVec j.
    have hcol : (fun i => (activeUnitary Θ a hα_pos : Matrix (Fin n) (Fin n) ℂ) i j) =
        activeRescaledVec Θ a j := by
      funext i
      rw [activeUnitary_col]
      rw [extendedBasis_apply_active Θ a hα_pos j hj_act]
      rfl
    rw [hcol]
    unfold activeRescaledVec
    -- Goal: Aᴴ b_j = (activeNorm) • ((activeNorm)⁻¹ • Aᴴ b_j) = Aᴴ b_j (when activeNorm ≠ 0).
    rw [smul_smul]
    have hσ_pos : 0 < (gramA_isHermitian Θ a).eigenvalues j :=
      lt_of_le_of_ne (gramA_eigenvalues_nonneg Θ a hα_pos j) (Ne.symm hj)
    have h_an_pos : 0 < activeNorm Θ a j := by
      unfold activeNorm; exact Real.sqrt_pos.mpr (mul_pos hα_pos hσ_pos)
    have h_an_ne : (activeNorm Θ a j : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt h_an_pos)
    rw [show (activeNorm Θ a j : ℂ) * (activeNorm Θ a j : ℂ)⁻¹ = 1 by
      field_simp]
    rw [one_smul]

/-- The diagonal matrix `diag(activeNorm Θ a 0, ..., activeNorm Θ a (n-1))`. -/
noncomputable def diagActiveNorm (Θ : HCParams n) (a : Fin n) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun i => (activeNorm Θ a i : ℂ))

/-- **Matrix-form structural identity.** `Aᴴ · U_X = Q_a · diag(activeNorm)`,
    where `U_X` is the eigenvector unitary of `gramA Θ a`. -/
theorem conjTranspose_mul_eigenvectorUnitary_eq (Θ : HCParams n) (a : Fin n)
    (hα_pos : 0 < (frobNormSq (Θ.A a)).re) :
    (Θ.A a).conjTranspose *
      ((gramA_isHermitian Θ a).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) =
    (activeUnitary Θ a hα_pos : Matrix (Fin n) (Fin n) ℂ) * diagActiveNorm Θ a := by
  ext i j
  -- LHS i j = (Aᴴ * U_X) i j = (Aᴴ ·ᵥ b_j) i.
  have hLHS : ((Θ.A a).conjTranspose *
      ((gramA_isHermitian Θ a).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)) i j =
      ((Θ.A a)ᴴ *ᵥ gramA_eigenvector Θ a j) i := by
    rw [Matrix.mul_apply]
    rw [show ((Θ.A a)ᴴ *ᵥ gramA_eigenvector Θ a j) i =
        ∑ k, (Θ.A a)ᴴ i k * gramA_eigenvector Θ a j k from rfl]
    rfl
  rw [hLHS]
  -- RHS i j = (Q_a * diag(activeNorm)) i j = Q_a i j * activeNorm Θ a j.
  rw [show ((activeUnitary Θ a hα_pos : Matrix (Fin n) (Fin n) ℂ) *
            diagActiveNorm Θ a) i j =
        (activeUnitary Θ a hα_pos : Matrix (Fin n) (Fin n) ℂ) i j *
          (activeNorm Θ a j : ℂ) from by
    unfold diagActiveNorm
    rw [Matrix.mul_diagonal]]
  -- Use conjTranspose_mulVec_eigenvector_eq.
  have h := conjTranspose_mulVec_eigenvector_eq Θ a j hα_pos
  have h_i := congrFun h i
  simp at h_i
  rw [h_i]
  ring

/-- `diagActiveNorm` is self-adjoint (real-diagonal). -/
theorem diagActiveNorm_conjTranspose (Θ : HCParams n) (a : Fin n) :
    (diagActiveNorm Θ a).conjTranspose = diagActiveNorm Θ a := by
  unfold diagActiveNorm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i; simp

/-- **Polar form of A.** `A_a = U_X · diagActiveNorm · Q_aᴴ`. -/
theorem A_eq_eigenvectorUnitary_diag_conjTranspose (Θ : HCParams n) (a : Fin n)
    (hα_pos : 0 < (frobNormSq (Θ.A a)).re) :
    Θ.A a =
    ((gramA_isHermitian Θ a).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      diagActiveNorm Θ a *
      (activeUnitary Θ a hα_pos : Matrix (Fin n) (Fin n) ℂ).conjTranspose := by
  -- From Aᴴ U = Q D, take conjTranspose: Uᴴ A = D Qᴴ.
  have hkey := conjTranspose_mul_eigenvectorUnitary_eq Θ a hα_pos
  have hkeyT : ((gramA_isHermitian Θ a).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).conjTranspose *
      Θ.A a =
      diagActiveNorm Θ a *
        (activeUnitary Θ a hα_pos : Matrix (Fin n) (Fin n) ℂ).conjTranspose := by
    have := congrArg Matrix.conjTranspose hkey
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.conjTranspose_mul, diagActiveNorm_conjTranspose] at this
    exact this
  -- Multiply by U on the left.
  have hUUH : ((gramA_isHermitian Θ a).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      ((gramA_isHermitian Θ a).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).conjTranspose = 1 := by
    have h := (gramA_isHermitian Θ a).eigenvectorUnitary.2
    rw [Matrix.mem_unitaryGroup_iff'] at h
    exact Matrix.mul_eq_one_comm.mpr h
  calc Θ.A a
      = (((gramA_isHermitian Θ a).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
          ((gramA_isHermitian Θ a).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).conjTranspose)
          * Θ.A a := by rw [hUUH, Matrix.one_mul]
    _ = ((gramA_isHermitian Θ a).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
          (((gramA_isHermitian Θ a).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).conjTranspose
            * Θ.A a) := by rw [Matrix.mul_assoc]
    _ = ((gramA_isHermitian Θ a).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
          (diagActiveNorm Θ a *
            (activeUnitary Θ a hα_pos : Matrix (Fin n) (Fin n) ℂ).conjTranspose) := by rw [hkeyT]
    _ = ((gramA_isHermitian Θ a).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
          diagActiveNorm Θ a *
          (activeUnitary Θ a hα_pos : Matrix (Fin n) (Fin n) ℂ).conjTranspose := by
        rw [← Matrix.mul_assoc]

/-- `A_a · Q_a = U_X · diagActiveNorm`. -/
theorem A_mul_activeUnitary_eq (Θ : HCParams n) (a : Fin n)
    (hα_pos : 0 < (frobNormSq (Θ.A a)).re) :
    Θ.A a * (activeUnitary Θ a hα_pos : Matrix (Fin n) (Fin n) ℂ) =
    ((gramA_isHermitian Θ a).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      diagActiveNorm Θ a := by
  rw [A_eq_eigenvectorUnitary_diag_conjTranspose Θ a hα_pos]
  rw [Matrix.mul_assoc, Matrix.mul_assoc]
  rw [show (activeUnitary Θ a hα_pos : Matrix (Fin n) (Fin n) ℂ).conjTranspose *
        (activeUnitary Θ a hα_pos : Matrix (Fin n) (Fin n) ℂ) = 1 from
      activeUnitary_conjTranspose_mul Θ a hα_pos]
  rw [Matrix.mul_one]

/-- `liftedUnitary` is unitary: `M · Mᴴ = 1`. -/
theorem liftedUnitary_mul_conjTranspose (Θ : HCParams n) (a : Fin n)
    (hα_pos : 0 < (frobNormSq (Θ.A a)).re) :
    liftedUnitary Θ a hα_pos * (liftedUnitary Θ a hα_pos).conjTranspose = 1 := by
  -- (U · Qᴴ) (U · Qᴴ)ᴴ = U · Qᴴ · Q · Uᴴ = U · 1 · Uᴴ = U Uᴴ = 1.
  unfold liftedUnitary
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [show
      ((gramA_isHermitian Θ a).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
        (activeUnitary Θ a hα_pos : Matrix (Fin n) (Fin n) ℂ).conjTranspose *
        ((activeUnitary Θ a hα_pos : Matrix (Fin n) (Fin n) ℂ) *
          ((gramA_isHermitian Θ a).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).conjTranspose) =
      ((gramA_isHermitian Θ a).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
        ((activeUnitary Θ a hα_pos : Matrix (Fin n) (Fin n) ℂ).conjTranspose *
          (activeUnitary Θ a hα_pos : Matrix (Fin n) (Fin n) ℂ)) *
        ((gramA_isHermitian Θ a).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).conjTranspose
      from by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]]
  rw [activeUnitary_conjTranspose_mul, Matrix.mul_one]
  -- U · Uᴴ = 1.
  have h := (gramA_isHermitian Θ a).eigenvectorUnitary.2
  rw [Matrix.mem_unitaryGroup_iff'] at h
  -- h : star U * U = 1, which is Uᴴ * U = 1. We want U * Uᴴ = 1. By square symmetry.
  exact Matrix.mul_eq_one_comm.mpr h

/-! ## Status note: active-subspace mechanisation in progress

The full discharge of `collinear_to_unitary_collinear` requires:

  1. Spectral decomposition of `X` (Hermitian above): `X = U_X · Σ · U_Xᴴ`
     with `U_X` unitary and `Σ` diagonal with real nonneg eigenvalues.
     **Mathlib has this** via `Matrix.IsHermitian.eigenvectorBasis` and
     `Matrix.IsHermitian.spectralTheorem`.

  2. Define active subspace `V := range X` (eigenvectors with nonzero
     eigenvalue). Dimension `r = rank X = κn`.

  3. Each `A_a` satisfies `A_a A_aᴴ = α_a · X`, so `range A_a ⊆ V`.
     In spectral coordinates, `Uᴴ A_a U` has the structure: the first
     `r` rows have squared norms `α_a · σ_i > 0`, and the last `n-r`
     rows are zero (correspond to zero eigenvalues of `Σ`).

  4. Define `Q_a` by:
        * Row `i` for `i ≤ r`: `(1/√(α_a σ_i)) · row_i (Uᴴ A_a U)`.
        * Row `i` for `i > r`: chosen orthonormal vector consistent
          across all `a`, `b`, `c`.

  5. Each `Q_a` is unitary. Lift back: `Θ'.A a := U · Q_a · Uᴴ`.

  6. Verify `Factorizes Θ' f` and `PerfectCollinearity Θ' f` using the
     consistent extension on the orthogonal complement.

This is roughly 500-1000 lines of careful Lean work. Status: foundation
laid (Hermitian + PSD properties of `gramA`); the substantial work of
steps 2-6 remains. -/

end
