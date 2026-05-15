/-
  HyperCubeGroup.ActiveSubspaceGeneric

  Active-subspace machinery parameterised over a generic matrix
  `M : Matrix (Fin n) (Fin n) ℂ` (with `frobNormSq M ≠ 0`).

  This module provides the abstract construction. Specialisations to
  the matrices `A_a`, `B_b`, and `(C_c)ᴴ` (for the C-side gram structure)
  are obtained by instantiation.

  Provides:
    * `gramOf M = (1/frobNormSq M) • (M · Mᴴ)`
    * Hermitian, PSD, eigenvalue / eigenvector machinery
    * `M_self_mul_conjTranspose_eigenvector` analog
    * Annihilation, active norm, orthogonality
    * `activeRescaledVec` and orthonormality
    * Extended ONB and active unitary `Q`
    * Polar decomposition `M = U · D · Qᴴ`
    * Lifted unitary `U · Qᴴ`
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

namespace ActiveSubspaceGeneric

variable {n : ℕ} [NeZero n]

/-! ## Generic gram matrix `gramOf M = (1/‖M‖²) • (M · Mᴴ)` -/

/-- Generic gram matrix associated with `M`. -/
noncomputable def gramOf (M : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / frobNormSq M) • (M * Mᴴ)

/-- The Gram matrix `gramOf M` is Hermitian. -/
theorem gramOf_isHermitian (M : Matrix (Fin n) (Fin n) ℂ) :
    (gramOf M).IsHermitian := by
  unfold gramOf
  show ((1 / frobNormSq M) • (M * Mᴴ))ᴴ =
       (1 / frobNormSq M) • (M * Mᴴ)
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  congr 1
  rw [star_div₀, star_one]
  exact congrArg (1 / ·) (star_frobNormSq _)

/-- `frobNormSq M` is real-valued. -/
theorem frobNormSq_eq_re_complex (M : Matrix (Fin n) (Fin n) ℂ) :
    frobNormSq M = ((frobNormSq M).re : ℂ) := by
  apply Complex.ext
  · simp
  · simp [frobNormSq_real]

/-- Trace of `gramOf M` equals `n` (when M is nonzero). -/
theorem trace_gramOf (M : Matrix (Fin n) (Fin n) ℂ)
    (hα_ne : frobNormSq M ≠ 0) :
    (gramOf M).trace = (n : ℂ) := by
  unfold gramOf
  rw [Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm,
      show (Mᴴ * M).trace = (n : ℂ) * frobNormSq M from ?_]
  · field_simp
  · unfold frobNormSq frobInner
    have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    field_simp

/-- For `M` with positive Frobenius norm, `1/frobNormSq M` is a nonneg complex. -/
theorem one_div_frobNormSq_nonneg (M : Matrix (Fin n) (Fin n) ℂ)
    (hα_pos : 0 < (frobNormSq M).re) :
    (0 : ℂ) ≤ 1 / frobNormSq M := by
  rw [Complex.le_def]
  have him : (frobNormSq M).im = 0 := frobNormSq_real _
  refine ⟨?_, ?_⟩
  · rw [show (0 : ℂ).re = 0 from rfl]
    rw [show (1 / frobNormSq M) = (frobNormSq M)⁻¹ from one_div _]
    rw [Complex.inv_re]
    rw [show Complex.normSq (frobNormSq M) = (frobNormSq M).re ^ 2 from ?_]
    · positivity
    · rw [Complex.normSq_apply, him]; ring
  · rw [show (0 : ℂ).im = 0 from rfl]
    rw [show (1 / frobNormSq M) = (frobNormSq M)⁻¹ from one_div _]
    rw [Complex.inv_im, him]
    simp

/-- The shared Gram matrix `gramOf M` is positive semidefinite. -/
theorem gramOf_posSemidef (M : Matrix (Fin n) (Fin n) ℂ)
    (hα_pos : 0 < (frobNormSq M).re) :
    Matrix.PosSemidef (gramOf M) := by
  show Matrix.PosSemidef ((1 / frobNormSq M) • (M * Mᴴ))
  apply Matrix.PosSemidef.smul (Matrix.posSemidef_self_mul_conjTranspose _)
  exact one_div_frobNormSq_nonneg M hα_pos

/-- Clean matrix identity: `M · Mᴴ = ‖M‖² · gramOf M`. -/
theorem M_mul_conjTranspose_eq_smul_gramOf (M : Matrix (Fin n) (Fin n) ℂ)
    (hα_ne : frobNormSq M ≠ 0) :
    M * Mᴴ = frobNormSq M • gramOf M := by
  show M * Mᴴ = frobNormSq M • ((1 / frobNormSq M) • (M * Mᴴ))
  rw [smul_smul,
      show frobNormSq M * (1 / frobNormSq M) = 1 from by field_simp]
  rw [one_smul]

/-! ## Eigenvalue / eigenvector machinery -/

/-- The eigenvalues of `gramOf M` are nonneg (by PSD). -/
theorem gramOf_eigenvalues_nonneg (M : Matrix (Fin n) (Fin n) ℂ)
    (hα_pos : 0 < (frobNormSq M).re) (i : Fin n) :
    0 ≤ (gramOf_isHermitian M).eigenvalues i :=
  Matrix.PosSemidef.eigenvalues_nonneg (gramOf_posSemidef M hα_pos) i

/-- Sum of eigenvalues of `gramOf M` equals `n`. -/
theorem gramOf_eigenvalues_sum (M : Matrix (Fin n) (Fin n) ℂ)
    (hα_ne : frobNormSq M ≠ 0) :
    ∑ i : Fin n, ((gramOf_isHermitian M).eigenvalues i : ℂ) = (n : ℂ) := by
  have h := (gramOf_isHermitian M).trace_eq_sum_eigenvalues
  exact h.symm.trans (trace_gramOf M hα_ne)

/-- The i-th eigenvector of `gramOf M`. -/
noncomputable def gramOf_eigenvector (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    Fin n → ℂ :=
  ((gramOf_isHermitian M).eigenvectorBasis i : EuclideanSpace ℂ (Fin n))

/-- The eigenvalue equation. -/
theorem gramOf_mulVec_eigenvector (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    (gramOf M) *ᵥ (gramOf_eigenvector M i) =
    ((gramOf_isHermitian M).eigenvalues i : ℂ) • (gramOf_eigenvector M i) :=
  (gramOf_isHermitian M).mulVec_eigenvectorBasis i

/-- `M · Mᴴ` acting on the i-th eigenvector. -/
theorem M_self_mul_conjTranspose_eigenvector (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    (M * Mᴴ) *ᵥ (gramOf_eigenvector M i) =
    (frobNormSq M * ((gramOf_isHermitian M).eigenvalues i : ℂ)) •
      (gramOf_eigenvector M i) := by
  have hg : gramOf M = (1 / frobNormSq M) • (M * Mᴴ) := rfl
  by_cases hα : frobNormSq M = 0
  · have hM_zero : M = 0 := (frobNormSq_eq_zero_iff _).mp hα
    rw [hα]
    rw [show M * Mᴴ = 0 from by rw [hM_zero]; simp]
    simp
  · have hMM : M * Mᴴ = frobNormSq M • gramOf M := by
      rw [hg, smul_smul,
          show frobNormSq M * (1 / frobNormSq M) = 1 from by field_simp]
      rw [one_smul]
    rw [hMM, Matrix.smul_mulVec, gramOf_mulVec_eigenvector, smul_smul]

/-- `M · Mᴴ` annihilates inactive eigenvectors. -/
theorem M_self_mul_conjTranspose_eigenvector_of_zero
    (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n)
    (hσ : (gramOf_isHermitian M).eigenvalues i = 0) :
    (M * Mᴴ) *ᵥ (gramOf_eigenvector M i) = 0 := by
  rw [M_self_mul_conjTranspose_eigenvector M i, hσ]
  simp

/-- `Mᴴ` annihilates inactive eigenvectors. -/
theorem conjTranspose_eigenvector_of_zero (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n)
    (hσ : (gramOf_isHermitian M).eigenvalues i = 0) :
    Mᴴ *ᵥ (gramOf_eigenvector M i) = 0 := by
  set b := gramOf_eigenvector M i with hb_def
  set v := Mᴴ *ᵥ b with hv_def
  have hAAH : M *ᵥ v = 0 := by
    show M *ᵥ (Mᴴ *ᵥ b) = 0
    rw [Matrix.mulVec_mulVec]
    exact M_self_mul_conjTranspose_eigenvector_of_zero M i hσ
  have hidentity : star v ⬝ᵥ v = star b ⬝ᵥ (M *ᵥ v) := by
    rw [show star v = star b ᵥ* M from ?_]
    · rw [← Matrix.dotProduct_mulVec]
    · rw [hv_def, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
  have hvv : star v ⬝ᵥ v = 0 := by
    rw [hidentity, hAAH, dotProduct_zero]
  exact dotProduct_star_self_eq_zero.mp hvv

/-! ## Orthonormality of the eigenvector basis -/

/-- The eigenvectors of `gramOf M` are unit vectors. -/
theorem gramOf_eigenvector_dotProduct_self (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    star (gramOf_eigenvector M i) ⬝ᵥ gramOf_eigenvector M i = 1 := by
  have horth : ‖(gramOf_isHermitian M).eigenvectorBasis i‖ = 1 :=
    (gramOf_isHermitian M).eigenvectorBasis.orthonormal.1 i
  have hinner :
      @inner ℂ _ _ ((gramOf_isHermitian M).eigenvectorBasis i)
        ((gramOf_isHermitian M).eigenvectorBasis i) = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, horth]
    simp
  rw [show star (gramOf_eigenvector M i) ⬝ᵥ gramOf_eigenvector M i =
        gramOf_eigenvector M i ⬝ᵥ star (gramOf_eigenvector M i)
        from dotProduct_comm _ _]
  rw [show gramOf_eigenvector M i ⬝ᵥ star (gramOf_eigenvector M i) =
        @inner ℂ _ _ ((gramOf_isHermitian M).eigenvectorBasis i)
          ((gramOf_isHermitian M).eigenvectorBasis i)
        from (EuclideanSpace.inner_eq_star_dotProduct _ _).symm]
  exact hinner

/-- Distinct eigenvectors are orthogonal. -/
theorem gramOf_eigenvector_dotProduct_of_ne (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n)
    (hij : i ≠ j) :
    star (gramOf_eigenvector M i) ⬝ᵥ gramOf_eigenvector M j = 0 := by
  have horth :
      @inner ℂ _ _ ((gramOf_isHermitian M).eigenvectorBasis i)
        ((gramOf_isHermitian M).eigenvectorBasis j) = (0 : ℂ) :=
    (gramOf_isHermitian M).eigenvectorBasis.orthonormal.2 hij
  rw [show star (gramOf_eigenvector M i) ⬝ᵥ gramOf_eigenvector M j =
        gramOf_eigenvector M j ⬝ᵥ star (gramOf_eigenvector M i)
        from dotProduct_comm _ _]
  rw [show gramOf_eigenvector M j ⬝ᵥ star (gramOf_eigenvector M i) =
        @inner ℂ _ _ ((gramOf_isHermitian M).eigenvectorBasis i)
          ((gramOf_isHermitian M).eigenvectorBasis j)
        from (EuclideanSpace.inner_eq_star_dotProduct _ _).symm]
  exact horth

/-! ## Active subspace norm and orthogonality -/

/-- `‖Mᴴ b_i‖² = α σ_i`. -/
theorem normSq_conjTranspose_mulVec_eigenvector (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    star (Mᴴ *ᵥ gramOf_eigenvector M i) ⬝ᵥ (Mᴴ *ᵥ gramOf_eigenvector M i) =
    frobNormSq M * ((gramOf_isHermitian M).eigenvalues i : ℂ) := by
  set b := gramOf_eigenvector M i with hb_def
  set v := Mᴴ *ᵥ b with hv_def
  have hAAv : M *ᵥ v =
      (frobNormSq M * ((gramOf_isHermitian M).eigenvalues i : ℂ)) • b := by
    show M *ᵥ (Mᴴ *ᵥ b) = _
    rw [Matrix.mulVec_mulVec]
    exact M_self_mul_conjTranspose_eigenvector M i
  have hidentity : star v ⬝ᵥ v = star b ⬝ᵥ (M *ᵥ v) := by
    rw [show star v = star b ᵥ* M from ?_]
    · rw [← Matrix.dotProduct_mulVec]
    · rw [hv_def, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
  rw [hidentity, hAAv, dotProduct_smul, smul_eq_mul,
      gramOf_eigenvector_dotProduct_self, mul_one]

/-- For distinct i, j: `Mᴴ b_i ⊥ Mᴴ b_j`. -/
theorem conjTranspose_mulVec_eigenvector_dotProduct_of_ne
    (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) (hij : i ≠ j) :
    star (Mᴴ *ᵥ gramOf_eigenvector M i) ⬝ᵥ
      (Mᴴ *ᵥ gramOf_eigenvector M j) = 0 := by
  set bi := gramOf_eigenvector M i with hbi_def
  set bj := gramOf_eigenvector M j with hbj_def
  set vi := Mᴴ *ᵥ bi with hvi_def
  set vj := Mᴴ *ᵥ bj with hvj_def
  have hAAvj : M *ᵥ vj =
      (frobNormSq M * ((gramOf_isHermitian M).eigenvalues j : ℂ)) • bj := by
    show M *ᵥ (Mᴴ *ᵥ bj) = _
    rw [Matrix.mulVec_mulVec]
    exact M_self_mul_conjTranspose_eigenvector M j
  have hidentity : star vi ⬝ᵥ vj = star bi ⬝ᵥ (M *ᵥ vj) := by
    rw [show star vi = star bi ᵥ* M from ?_]
    · rw [← Matrix.dotProduct_mulVec]
    · rw [hvi_def, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
  rw [hidentity, hAAvj, dotProduct_smul, smul_eq_mul,
      gramOf_eigenvector_dotProduct_of_ne M i j hij, mul_zero]

/-! ## Active rescaled vectors `c_i := (1/√(α σ_i)) Mᴴ b_i` -/

/-- The active norm `√(α · σ_i)` as a real number. -/
noncomputable def activeNorm (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : ℝ :=
  Real.sqrt ((frobNormSq M).re * (gramOf_isHermitian M).eigenvalues i)

/-- The active rescaled vector. -/
noncomputable def activeRescaledVec (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    Fin n → ℂ :=
  ((activeNorm M i : ℂ)⁻¹) • (Mᴴ *ᵥ gramOf_eigenvector M i)

/-- Active rescaled vectors are unit-norm (for active i and α > 0). -/
theorem activeRescaledVec_dotProduct_self (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n)
    (hα_pos : 0 < (frobNormSq M).re)
    (hσ_pos : 0 < (gramOf_isHermitian M).eigenvalues i) :
    star (activeRescaledVec M i) ⬝ᵥ activeRescaledVec M i = 1 := by
  unfold activeRescaledVec
  rw [star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      normSq_conjTranspose_mulVec_eigenvector, frobNormSq_eq_re_complex]
  set α := (frobNormSq M).re with hα_def
  set σ := (gramOf_isHermitian M).eigenvalues i with hσ_def
  have hαnn : 0 ≤ α := le_of_lt hα_pos
  have hσnn : 0 ≤ σ := le_of_lt hσ_pos
  have h_an_sq_R : (activeNorm M i)^2 = α * σ := by
    unfold activeNorm; exact Real.sq_sqrt (mul_nonneg hαnn hσnn)
  have h_an_pos : 0 < activeNorm M i := by
    unfold activeNorm; exact Real.sqrt_pos.mpr (mul_pos hα_pos hσ_pos)
  have h_an_ne : (activeNorm M i : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt h_an_pos)
  have hstar : star ((activeNorm M i : ℂ)⁻¹) = (activeNorm M i : ℂ)⁻¹ := by
    rw [show (activeNorm M i : ℂ)⁻¹ = ((activeNorm M i)⁻¹ : ℂ) from by push_cast; rfl]
    simp
  rw [hstar]
  have h_an_sq_C : (activeNorm M i : ℂ) * (activeNorm M i : ℂ) =
      (α : ℂ) * (σ : ℂ) := by
    have : ((activeNorm M i)^2 : ℂ) = ((α * σ : ℝ) : ℂ) := by
      exact_mod_cast h_an_sq_R
    rw [show (activeNorm M i : ℂ) * (activeNorm M i : ℂ) =
          ((activeNorm M i)^2 : ℂ) from by push_cast; ring]
    rw [this]; push_cast; ring
  rw [show ((activeNorm M i : ℂ)⁻¹) * ((activeNorm M i : ℂ)⁻¹ *
        ((α : ℂ) * (σ : ℂ))) =
        ((α : ℂ) * (σ : ℂ)) /
        ((activeNorm M i : ℂ) * (activeNorm M i : ℂ))
        from by field_simp]
  rw [h_an_sq_C, div_self]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hα_pos))
    (Complex.ofReal_ne_zero.mpr (ne_of_gt hσ_pos))

/-- Distinct active rescaled vectors are orthogonal. -/
theorem activeRescaledVec_dotProduct_of_ne (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n)
    (hij : i ≠ j) :
    star (activeRescaledVec M i) ⬝ᵥ activeRescaledVec M j = 0 := by
  unfold activeRescaledVec
  rw [star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      conjTranspose_mulVec_eigenvector_dotProduct_of_ne M i j hij,
      mul_zero, mul_zero]

/-! ## Orthonormal extension -/

/-- The active set: indices i with σ_i ≠ 0. -/
def activeSet (M : Matrix (Fin n) (Fin n) ℂ) : Set (Fin n) :=
  {i | (gramOf_isHermitian M).eigenvalues i ≠ 0}

/-- Active rescaled vector lifted to EuclideanSpace. -/
noncomputable def activeRescaledLp (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (activeRescaledVec M i)

@[simp] lemma activeRescaledLp_apply (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    activeRescaledLp M i j = activeRescaledVec M i j := rfl

/-- Active rescaled vectors restricted to active set are orthonormal. -/
theorem orthonormal_activeRescaledLp_restrict (M : Matrix (Fin n) (Fin n) ℂ)
    (hα_pos : 0 < (frobNormSq M).re) :
    Orthonormal ℂ ((activeSet M).restrict (activeRescaledLp M)) := by
  rw [orthonormal_iff_ite]
  intro ⟨i, hi⟩ ⟨j, hj⟩
  simp only [Set.restrict_apply]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  rw [show
      WithLp.ofLp (activeRescaledLp M j) ⬝ᵥ star (WithLp.ofLp (activeRescaledLp M i))
      = star (activeRescaledVec M i) ⬝ᵥ activeRescaledVec M j from by
    rw [show WithLp.ofLp (activeRescaledLp M j) = activeRescaledVec M j from rfl,
        show WithLp.ofLp (activeRescaledLp M i) = activeRescaledVec M i from rfl]
    exact dotProduct_comm _ _]
  by_cases hij : i = j
  · subst hij
    simp only [Subtype.mk.injEq, if_true]
    have hσ_pos : 0 < (gramOf_isHermitian M).eigenvalues i := by
      have hσnn := gramOf_eigenvalues_nonneg M hα_pos i
      have hσne : (gramOf_isHermitian M).eigenvalues i ≠ 0 := hi
      exact lt_of_le_of_ne hσnn (Ne.symm hσne)
    exact activeRescaledVec_dotProduct_self M i hα_pos hσ_pos
  · simp only [Subtype.mk.injEq, hij, if_false]
    exact activeRescaledVec_dotProduct_of_ne M i j hij

/-- Existence of an extended ONB. -/
theorem exists_extended_orthonormalBasis (M : Matrix (Fin n) (Fin n) ℂ)
    (hα_pos : 0 < (frobNormSq M).re) :
    ∃ b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)),
      ∀ i ∈ activeSet M, b i = activeRescaledLp M i := by
  have hcard : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = Fintype.card (Fin n) := by
    rw [finrank_euclideanSpace_fin, Fintype.card_fin]
  exact (orthonormal_activeRescaledLp_restrict M hα_pos).exists_orthonormalBasis_extension_of_card_eq hcard

/-- The chosen extended ONB. -/
noncomputable def extendedBasis (M : Matrix (Fin n) (Fin n) ℂ)
    (hα_pos : 0 < (frobNormSq M).re) :
    OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)) :=
  Classical.choose (exists_extended_orthonormalBasis M hα_pos)

theorem extendedBasis_apply_active (M : Matrix (Fin n) (Fin n) ℂ)
    (hα_pos : 0 < (frobNormSq M).re)
    (i : Fin n) (hi : i ∈ activeSet M) :
    extendedBasis M hα_pos i = activeRescaledLp M i :=
  Classical.choose_spec (exists_extended_orthonormalBasis M hα_pos) i hi

/-! ## Active unitary `Q` -/

/-- The active unitary `Q_M`. -/
noncomputable def activeUnitary (M : Matrix (Fin n) (Fin n) ℂ)
    (hα_pos : 0 < (frobNormSq M).re) :
    Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨(EuclideanSpace.basisFun (Fin n) ℂ).toBasis.toMatrix
      (extendedBasis M hα_pos).toBasis,
   (EuclideanSpace.basisFun (Fin n) ℂ).toMatrix_orthonormalBasis_mem_unitary
      (extendedBasis M hα_pos)⟩

theorem activeUnitary_mul_conjTranspose (M : Matrix (Fin n) (Fin n) ℂ)
    (hα_pos : 0 < (frobNormSq M).re) :
    (activeUnitary M hα_pos : Matrix (Fin n) (Fin n) ℂ) *
      (activeUnitary M hα_pos : Matrix (Fin n) (Fin n) ℂ).conjTranspose = 1 :=
  (EuclideanSpace.basisFun (Fin n) ℂ).toMatrix_orthonormalBasis_self_mul_conjTranspose
    (extendedBasis M hα_pos)

theorem activeUnitary_conjTranspose_mul (M : Matrix (Fin n) (Fin n) ℂ)
    (hα_pos : 0 < (frobNormSq M).re) :
    (activeUnitary M hα_pos : Matrix (Fin n) (Fin n) ℂ).conjTranspose *
      (activeUnitary M hα_pos : Matrix (Fin n) (Fin n) ℂ) = 1 :=
  (EuclideanSpace.basisFun (Fin n) ℂ).toMatrix_orthonormalBasis_conjTranspose_mul_self
    (extendedBasis M hα_pos)

theorem activeUnitary_col (M : Matrix (Fin n) (Fin n) ℂ)
    (hα_pos : 0 < (frobNormSq M).re) (i j : Fin n) :
    (activeUnitary M hα_pos : Matrix (Fin n) (Fin n) ℂ) i j =
    (extendedBasis M hα_pos j : EuclideanSpace ℂ (Fin n)) i := rfl

/-! ## Structural identity: `Mᴴ b_j = activeNorm_j · column_j(Q)` -/

theorem conjTranspose_mulVec_eigenvector_eq (M : Matrix (Fin n) (Fin n) ℂ) (j : Fin n)
    (hα_pos : 0 < (frobNormSq M).re) :
    Mᴴ *ᵥ gramOf_eigenvector M j =
    (activeNorm M j : ℂ) •
      (fun i => (activeUnitary M hα_pos : Matrix (Fin n) (Fin n) ℂ) i j) := by
  by_cases hj : (gramOf_isHermitian M).eigenvalues j = 0
  · rw [conjTranspose_eigenvector_of_zero M j hj]
    have h_an_zero : activeNorm M j = 0 := by
      unfold activeNorm; rw [hj, mul_zero, Real.sqrt_zero]
    rw [h_an_zero]; simp
  · have hj_act : j ∈ activeSet M := hj
    have hcol : (fun i => (activeUnitary M hα_pos : Matrix (Fin n) (Fin n) ℂ) i j) =
        activeRescaledVec M j := by
      funext i
      rw [activeUnitary_col]
      rw [extendedBasis_apply_active M hα_pos j hj_act]
      rfl
    rw [hcol]
    unfold activeRescaledVec
    rw [smul_smul]
    have hσ_pos : 0 < (gramOf_isHermitian M).eigenvalues j :=
      lt_of_le_of_ne (gramOf_eigenvalues_nonneg M hα_pos j) (Ne.symm hj)
    have h_an_pos : 0 < activeNorm M j := by
      unfold activeNorm; exact Real.sqrt_pos.mpr (mul_pos hα_pos hσ_pos)
    have h_an_ne : (activeNorm M j : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt h_an_pos)
    rw [show (activeNorm M j : ℂ) * (activeNorm M j : ℂ)⁻¹ = 1 by field_simp]
    rw [one_smul]

/-- Diagonal matrix `diag(activeNorm)`. -/
noncomputable def diagActiveNorm (M : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun i => (activeNorm M i : ℂ))

theorem diagActiveNorm_conjTranspose (M : Matrix (Fin n) (Fin n) ℂ) :
    (diagActiveNorm M).conjTranspose = diagActiveNorm M := by
  unfold diagActiveNorm
  rw [Matrix.diagonal_conjTranspose]
  congr 1; funext i; simp

/-- Matrix-form structural identity: `Mᴴ · U = Q · D`. -/
theorem conjTranspose_mul_eigenvectorUnitary_eq (M : Matrix (Fin n) (Fin n) ℂ)
    (hα_pos : 0 < (frobNormSq M).re) :
    Mᴴ *
      ((gramOf_isHermitian M).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) =
    (activeUnitary M hα_pos : Matrix (Fin n) (Fin n) ℂ) * diagActiveNorm M := by
  ext i j
  have hLHS : (Mᴴ *
      ((gramOf_isHermitian M).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)) i j =
      (Mᴴ *ᵥ gramOf_eigenvector M j) i := by
    rw [Matrix.mul_apply]; rfl
  rw [hLHS]
  rw [show ((activeUnitary M hα_pos : Matrix (Fin n) (Fin n) ℂ) *
            diagActiveNorm M) i j =
        (activeUnitary M hα_pos : Matrix (Fin n) (Fin n) ℂ) i j *
          (activeNorm M j : ℂ) from by
    unfold diagActiveNorm; rw [Matrix.mul_diagonal]]
  have h := conjTranspose_mulVec_eigenvector_eq M j hα_pos
  have h_i := congrFun h i
  simp at h_i
  rw [h_i]; ring

/-- **Polar form**: `M = U · D · Qᴴ`. -/
theorem M_eq_eigenvectorUnitary_diag_conjTranspose (M : Matrix (Fin n) (Fin n) ℂ)
    (hα_pos : 0 < (frobNormSq M).re) :
    M =
    ((gramOf_isHermitian M).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      diagActiveNorm M *
      (activeUnitary M hα_pos : Matrix (Fin n) (Fin n) ℂ).conjTranspose := by
  have hkey := conjTranspose_mul_eigenvectorUnitary_eq M hα_pos
  have hkeyT : ((gramOf_isHermitian M).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).conjTranspose *
      M =
      diagActiveNorm M *
        (activeUnitary M hα_pos : Matrix (Fin n) (Fin n) ℂ).conjTranspose := by
    have := congrArg Matrix.conjTranspose hkey
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.conjTranspose_mul, diagActiveNorm_conjTranspose] at this
    exact this
  have hUUH : ((gramOf_isHermitian M).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      ((gramOf_isHermitian M).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).conjTranspose = 1 := by
    have h := (gramOf_isHermitian M).eigenvectorUnitary.2
    rw [Matrix.mem_unitaryGroup_iff'] at h
    exact Matrix.mul_eq_one_comm.mpr h
  calc M
      = (((gramOf_isHermitian M).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
          ((gramOf_isHermitian M).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).conjTranspose)
          * M := by rw [hUUH, Matrix.one_mul]
    _ = ((gramOf_isHermitian M).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
          (((gramOf_isHermitian M).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).conjTranspose
            * M) := by rw [Matrix.mul_assoc]
    _ = ((gramOf_isHermitian M).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
          (diagActiveNorm M *
            (activeUnitary M hα_pos : Matrix (Fin n) (Fin n) ℂ).conjTranspose) := by rw [hkeyT]
    _ = ((gramOf_isHermitian M).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
          diagActiveNorm M *
          (activeUnitary M hα_pos : Matrix (Fin n) (Fin n) ℂ).conjTranspose := by
        rw [← Matrix.mul_assoc]

theorem M_mul_activeUnitary_eq (M : Matrix (Fin n) (Fin n) ℂ)
    (hα_pos : 0 < (frobNormSq M).re) :
    M * (activeUnitary M hα_pos : Matrix (Fin n) (Fin n) ℂ) =
    ((gramOf_isHermitian M).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      diagActiveNorm M := by
  set U := ((gramOf_isHermitian M).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
  set Q := (activeUnitary M hα_pos : Matrix (Fin n) (Fin n) ℂ)
  set D := diagActiveNorm M
  have hM_polar : M = U * D * Qᴴ :=
    M_eq_eigenvectorUnitary_diag_conjTranspose M hα_pos
  have hQHQ : Qᴴ * Q = 1 := activeUnitary_conjTranspose_mul M hα_pos
  calc M * Q = (U * D * Qᴴ) * Q := by rw [hM_polar]
    _ = U * D * (Qᴴ * Q) := by rw [Matrix.mul_assoc]
    _ = U * D * 1 := by rw [hQHQ]
    _ = U * D := by rw [Matrix.mul_one]

/-! ## Lifted unitary `U · Qᴴ` -/

/-- Lifted unitary candidate: `U · Qᴴ`. -/
noncomputable def liftedUnitary (M : Matrix (Fin n) (Fin n) ℂ)
    (hα_pos : 0 < (frobNormSq M).re) :
    Matrix (Fin n) (Fin n) ℂ :=
  ((gramOf_isHermitian M).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
    (activeUnitary M hα_pos : Matrix (Fin n) (Fin n) ℂ).conjTranspose

theorem liftedUnitary_mul_conjTranspose (M : Matrix (Fin n) (Fin n) ℂ)
    (hα_pos : 0 < (frobNormSq M).re) :
    liftedUnitary M hα_pos * (liftedUnitary M hα_pos).conjTranspose = 1 := by
  unfold liftedUnitary
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [show
      ((gramOf_isHermitian M).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
        (activeUnitary M hα_pos : Matrix (Fin n) (Fin n) ℂ).conjTranspose *
        ((activeUnitary M hα_pos : Matrix (Fin n) (Fin n) ℂ) *
          ((gramOf_isHermitian M).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).conjTranspose) =
      ((gramOf_isHermitian M).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
        ((activeUnitary M hα_pos : Matrix (Fin n) (Fin n) ℂ).conjTranspose *
          (activeUnitary M hα_pos : Matrix (Fin n) (Fin n) ℂ)) *
        ((gramOf_isHermitian M).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).conjTranspose
      from by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]]
  rw [activeUnitary_conjTranspose_mul, Matrix.mul_one]
  have h := (gramOf_isHermitian M).eigenvectorUnitary.2
  rw [Matrix.mem_unitaryGroup_iff'] at h
  exact Matrix.mul_eq_one_comm.mpr h

/-- Other-direction unitarity: `Lᴴ · L = 1`. -/
theorem liftedUnitary_conjTranspose_mul (M : Matrix (Fin n) (Fin n) ℂ)
    (hα_pos : 0 < (frobNormSq M).re) :
    (liftedUnitary M hα_pos).conjTranspose * liftedUnitary M hα_pos = 1 :=
  Matrix.mul_eq_one_comm.mpr (liftedUnitary_mul_conjTranspose M hα_pos)

end ActiveSubspaceGeneric

end
