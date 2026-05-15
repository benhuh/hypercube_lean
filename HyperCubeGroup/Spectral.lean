/-
  HyperCubeGroup.Spectral

  Spectral-theory lemmas used by the matrix AM-GM proof.

  Single foundational axiom: `matrix_unitary_schur_form`. From it we
  derive `schur_inequality_diag_form` for arbitrary complex matrices.

  Mathlib has all the constituent pieces (eigenspace decomposition,
  Gram-Schmidt, Frobenius norm) but does not yet package the unitary
  Schur form as a single named theorem; ~150 lines of new Lean would
  assemble it via the standard induction-on-dimension proof.
-/

import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import HyperCubeGroup.Basic

open Matrix BigOperators Complex

noncomputable section

variable {n : ℕ}

/-! ## Unnormalised Frobenius norm squared -/

/-- Unnormalised Frobenius norm squared `Σ_{i,j} |A_{ij}|²` (real).
    Generalised to any finite index type so it applies to block matrices
    indexed by `Fin 3 × Fin n` etc. -/
def frobNormSq_F {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) : ℝ :=
  ∑ i : ι, ∑ j : ι, Complex.normSq (A i j)

theorem frobNormSq_F_nonneg {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) :
    0 ≤ frobNormSq_F A := by
  unfold frobNormSq_F
  apply Finset.sum_nonneg; intros i _
  apply Finset.sum_nonneg; intros j _
  exact Complex.normSq_nonneg _

/-- `Σ_{ij} |A_{ij}|² = Tr(Aᴴ · A).re`. -/
theorem frobNormSq_F_eq_trace_re {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    frobNormSq_F A = ((Aᴴ * A).trace).re := by
  have hentry : ∀ i : ι,
      ((Aᴴ * A) i i).re = ∑ j : ι, Complex.normSq (A j i) := by
    intro i
    rw [Matrix.mul_apply, Complex.re_sum]
    apply Finset.sum_congr rfl
    intros j _
    rw [Matrix.conjTranspose_apply]
    rw [show (star (A j i) : ℂ) = (starRingEnd ℂ) (A j i) from rfl]
    rw [← Complex.normSq_eq_conj_mul_self]
    exact Complex.ofReal_re _
  unfold frobNormSq_F
  rw [Matrix.trace, Complex.re_sum]
  rw [show (∑ i : ι, ((Aᴴ * A).diag i).re)
        = ∑ i : ι, ∑ j : ι, Complex.normSq (A j i) from ?_]
  · rw [Finset.sum_comm]
  · apply Finset.sum_congr rfl
    intros i _
    exact hentry i

/-! ## Unitary invariance of Frobenius norm squared -/

/-- For unitary `U` (with `Uᴴ * U = 1`), `‖U · M‖²_F = ‖M‖²_F`. -/
theorem frobNormSq_F_unitary_mul_left {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U M : Matrix ι ι ℂ) (hU : Uᴴ * U = 1) :
    frobNormSq_F (U * M) = frobNormSq_F M := by
  rw [frobNormSq_F_eq_trace_re (U * M), frobNormSq_F_eq_trace_re M]
  congr 1
  -- Tr((U M)ᴴ (U M)) = Tr(Mᴴ Uᴴ U M) = Tr(Mᴴ M)
  rw [Matrix.conjTranspose_mul]
  rw [show Mᴴ * Uᴴ * (U * M) = Mᴴ * (Uᴴ * U) * M from by simp only [Matrix.mul_assoc]]
  rw [hU, Matrix.mul_one]

/-- For unitary `U` (with `U * Uᴴ = 1`), `‖M · U‖²_F = ‖M‖²_F`. -/
theorem frobNormSq_F_unitary_mul_right {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M U : Matrix ι ι ℂ) (hU : U * Uᴴ = 1) :
    frobNormSq_F (M * U) = frobNormSq_F M := by
  rw [frobNormSq_F_eq_trace_re (M * U), frobNormSq_F_eq_trace_re M]
  congr 1
  -- Tr((M U)ᴴ (M U)) = Tr(Uᴴ Mᴴ M U) = Tr(Mᴴ M U Uᴴ) = Tr(Mᴴ M)
  rw [Matrix.conjTranspose_mul]
  rw [show (Uᴴ * Mᴴ) * (M * U) = Uᴴ * (Mᴴ * M * U) from by
        simp only [Matrix.mul_assoc]]
  rw [Matrix.trace_mul_comm Uᴴ (Mᴴ * M * U)]
  -- Goal: (Mᴴ * M * U * Uᴴ).trace = (Mᴴ * M).trace
  rw [show Mᴴ * M * U * Uᴴ = Mᴴ * M * (U * Uᴴ) from by
        simp only [Matrix.mul_assoc]]
  rw [hU, Matrix.mul_one]

/-- **Equality case** of the triangle inequality: if `Σ ‖z_i‖ = (Σ z_i).re`,
    then each `z_i` is a nonneg real number. -/
theorem norm_sum_eq_re_sum_imp_each_nonneg_real
    {ι : Type*} [Fintype ι] (z : ι → ℂ)
    (heq : ∑ i : ι, ‖z i‖ = (∑ i : ι, z i).re) :
    ∀ i, (z i).im = 0 ∧ 0 ≤ (z i).re := by
  -- Σ Re(z_i) = Σ ‖z_i‖, with term-wise (z_i).re ≤ ‖z_i‖.
  -- So each ‖z_i‖ - (z_i).re ≥ 0, sum = 0, each = 0.
  have hsum_re : (∑ i : ι, z i).re = ∑ i : ι, (z i).re := by
    rw [Complex.re_sum]
  rw [hsum_re] at heq
  have hterm_nn : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ ‖z i‖ - (z i).re := by
    intros i _
    have : (z i).re ≤ ‖z i‖ := Complex.re_le_norm (z i)
    linarith
  have hsum_diff : ∑ i : ι, (‖z i‖ - (z i).re) = 0 := by
    rw [Finset.sum_sub_distrib]; linarith
  have h_each : ∀ i ∈ (Finset.univ : Finset ι), ‖z i‖ - (z i).re = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hterm_nn).mp hsum_diff
  intro i
  have hi : ‖z i‖ = (z i).re :=
    sub_eq_zero.mp (h_each i (Finset.mem_univ _))
  have hre_nn : 0 ≤ (z i).re := by rw [← hi]; exact norm_nonneg _
  refine ⟨?_, hre_nn⟩
  -- ‖z‖ = re z ⇒ im z = 0 (and re z ≥ 0). Use the RCLike formulation.
  exact RCLike.im_eq_zero_of_le (le_of_eq hi)

/-! ## Reindexing preserves Frobenius² and trace -/

/-- Frobenius² is invariant under reindexing by an `Equiv`. -/
theorem frobNormSq_F_submatrix_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (M : Matrix β β ℂ) :
    frobNormSq_F (M.submatrix e e) = frobNormSq_F M := by
  unfold frobNormSq_F
  rw [← e.sum_comp (fun i => ∑ j : β, Complex.normSq (M i j))]
  apply Finset.sum_congr rfl
  intros a _
  rw [← e.sum_comp (fun j => Complex.normSq (M (e a) j))]
  apply Finset.sum_congr rfl
  intros b _
  rfl

/-- Trace is invariant under reindexing by an `Equiv`. -/
theorem trace_submatrix_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (M : Matrix β β ℂ) :
    (M.submatrix e e).trace = M.trace := by
  unfold Matrix.trace Matrix.diag
  exact e.sum_comp (fun i => M i i)

/-! ## Diagonal sum is bounded by Frobenius² -/

/-- For any matrix `M`, the sum of squared moduli of diagonal entries
    is bounded by the Frobenius² norm. (Upper-triangularity not
    required for this direction.) -/
theorem frobNormSq_F_ge_sum_diag {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) :
    (∑ i : ι, Complex.normSq (M i i)) ≤ frobNormSq_F M := by
  unfold frobNormSq_F
  apply Finset.sum_le_sum
  intros i _
  calc Complex.normSq (M i i)
      = ∑ j ∈ ({i} : Finset ι), Complex.normSq (M i j) := by
        rw [Finset.sum_singleton]
    _ ≤ ∑ j : ι, Complex.normSq (M i j) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.subset_univ _
        · intros j _ _; exact Complex.normSq_nonneg _

/-- Equality case: `Σ |M_{ii}|² = ‖M‖²_F` iff all off-diagonal entries vanish. -/
theorem frobNormSq_F_eq_sum_diag_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) :
    (∑ i : ι, Complex.normSq (M i i)) = frobNormSq_F M ↔
    ∀ i j : ι, i ≠ j → M i j = 0 := by
  constructor
  · intro heq i j hij
    -- frobNormSq_F M = Σ_i Σ_j |M_ij|² = (Σ |M_ii|²) + Σ_{i≠j} |M_ij|².
    -- If equality, the off-diagonal sum is zero.
    have hsplit : frobNormSq_F M = (∑ i : ι, Complex.normSq (M i i)) +
                  ∑ i : ι, ∑ j ∈ (Finset.univ.erase i), Complex.normSq (M i j) := by
      unfold frobNormSq_F
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intros k _
      have h_split_k :
          (∑ j : ι, Complex.normSq (M k j)) =
          Complex.normSq (M k k) + ∑ j ∈ Finset.univ.erase k, Complex.normSq (M k j) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
      exact h_split_k
    rw [hsplit] at heq
    have hoff_zero :
        ∑ i : ι, ∑ j ∈ (Finset.univ.erase i), Complex.normSq (M i j) = 0 := by
      linarith
    have h_each_outer :
        ∀ i ∈ (Finset.univ : Finset ι),
          ∑ j ∈ (Finset.univ.erase i), Complex.normSq (M i j) = 0 := by
      apply (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => ?_)).mp hoff_zero
      apply Finset.sum_nonneg; intros j _; exact Complex.normSq_nonneg _
    have h_each_inner :
        ∀ k ∈ (Finset.univ.erase i), Complex.normSq (M i k) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg _)).mp
        (h_each_outer i (Finset.mem_univ _))
    have hj : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ _⟩
    have := h_each_inner j hj
    exact (Complex.normSq_eq_zero).mp this
  · intro hoff
    unfold frobNormSq_F
    -- Σ_i Σ_j |M_ij|² = Σ_i |M_ii|² + Σ_i Σ_{j≠i} |M_ij|², the latter is zero.
    have : ∀ i : ι, (∑ j : ι, Complex.normSq (M i j)) = Complex.normSq (M i i) := by
      intro i
      rw [show (Finset.univ : Finset ι) = insert i (Finset.univ.erase i) from
        (Finset.insert_erase (Finset.mem_univ i)).symm]
      rw [Finset.sum_insert (Finset.notMem_erase i _)]
      have : ∀ j ∈ Finset.univ.erase i, Complex.normSq (M i j) = 0 := by
        intros j hj
        rw [hoff i j (Ne.symm (Finset.ne_of_mem_erase hj))]
        exact Complex.normSq_zero
      rw [Finset.sum_eq_zero this, add_zero]
    simp_rw [this]

/-! ## Upper triangular predicate -/

/-- A matrix is upper triangular if all entries strictly below the
    diagonal vanish. Polymorphic in the (linearly ordered) index type
    so it applies both to `Matrix (Fin n) (Fin n)` and to reindexed
    block matrices. -/
def IsUpperTriangular {ι : Type*} [LT ι] (M : Matrix ι ι ℂ) : Prop :=
  ∀ i j : ι, j < i → M i j = 0

/-- The product of two upper-triangular matrices is upper triangular. -/
theorem IsUpperTriangular.mul {ι : Type*} [Fintype ι] [LinearOrder ι]
    {S T : Matrix ι ι ℂ}
    (hS : IsUpperTriangular S) (hT : IsUpperTriangular T) :
    IsUpperTriangular (S * T) := by
  intros i j hji
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intros k _
  by_cases hki : k < i
  · rw [hS i k hki]; ring
  · push_neg at hki
    have hjk : j < k := lt_of_lt_of_le hji hki
    rw [hT k j hjk]; ring

/-- The diagonal entry `(T · T)_{ii}` equals `T_{ii}²` for upper
    triangular `T`. -/
theorem IsUpperTriangular.diag_mul_self {ι : Type*} [Fintype ι] [LinearOrder ι]
    {T : Matrix ι ι ℂ} (hT : IsUpperTriangular T) (i : ι) :
    (T * T) i i = (T i i) ^ 2 := by
  rw [Matrix.mul_apply, sq]
  apply Finset.sum_eq_single i
  · intros k _ hki
    rcases lt_or_gt_of_ne hki with h | h
    · rw [hT i k h]; ring
    · rw [hT k i h]; ring
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- `Σ_i |T_{ii}|⁴ ≤ ‖T · T‖²_F` for upper triangular `T`. Direct
    corollary of `frobNormSq_F_ge_sum_diag` applied to `T · T` plus
    `(T·T)_{ii} = T_{ii}²`. -/
theorem IsUpperTriangular.sum_diag_pow_four_le
    {ι : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq ι]
    {T : Matrix ι ι ℂ} (hT : IsUpperTriangular T) :
    (∑ i : ι, Complex.normSq (T i i) ^ 2) ≤ frobNormSq_F (T * T) := by
  have hdiag : ∀ i : ι, Complex.normSq ((T * T) i i) = Complex.normSq (T i i) ^ 2 := by
    intro i
    rw [hT.diag_mul_self i, map_pow]
  rw [show (∑ i : ι, Complex.normSq (T i i) ^ 2)
        = ∑ i : ι, Complex.normSq ((T * T) i i) from by
      apply Finset.sum_congr rfl; intros i _; exact (hdiag i).symm]
  exact frobNormSq_F_ge_sum_diag (T * T)

/-- The diagonal entry `(T · T · T)_{ii}` equals `T_{ii}³` for upper
    triangular `T`. Proof: in `Σ_k (T·T)_{ik} · T_{ki}`, only the `k = i`
    term survives — for `k > i` the factor `T_{ki} = 0`; for `k < i`,
    `(T·T)_{ik} = Σ_j T_{ij} T_{jk}` requires `i ≤ j ≤ k`, impossible
    when `k < i`. -/
theorem IsUpperTriangular.diag_mul_self_mul_self
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    {T : Matrix ι ι ℂ} (hT : IsUpperTriangular T) (i : ι) :
    (T * T * T) i i = (T i i) ^ 3 := by
  rw [Matrix.mul_apply]
  have hTT : IsUpperTriangular (T * T) := hT.mul hT
  rw [show (∑ k : ι, (T * T) i k * T k i) = (T * T) i i * T i i from by
    apply Finset.sum_eq_single i
    · intros k _ hki
      rcases lt_or_gt_of_ne hki with h | h
      · rw [hTT i k h]; ring
      · rw [hT k i h]; ring
    · intro hi; exact absurd (Finset.mem_univ i) hi]
  rw [hT.diag_mul_self i]; ring

/-- `Tr(T · T · T) = Σ_i T_{ii}³` for upper triangular `T`. -/
theorem IsUpperTriangular.trace_mul_self_mul_self
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    {T : Matrix ι ι ℂ} (hT : IsUpperTriangular T) :
    (T * T * T).trace = ∑ i : ι, (T i i) ^ 3 := by
  unfold Matrix.trace Matrix.diag
  apply Finset.sum_congr rfl
  intros i _
  exact hT.diag_mul_self_mul_self i

/-- Trace-triangle inequality for upper triangular `T`:
    `‖Tr(T·T·T)‖ ≤ Σ_i ‖T_{ii}‖³`. -/
theorem IsUpperTriangular.norm_trace_cubed_le
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    {T : Matrix ι ι ℂ} (hT : IsUpperTriangular T) :
    ‖(T * T * T).trace‖ ≤ ∑ i : ι, ‖T i i‖ ^ 3 := by
  rw [hT.trace_mul_self_mul_self]
  refine le_trans (norm_sum_le _ _) ?_
  apply Finset.sum_le_sum
  intros i _
  rw [show (T i i) ^ 3 = T i i * T i i * T i i from by ring]
  exact le_of_eq (by rw [norm_mul, norm_mul]; ring)

/-- Power-mean Hölder bound (elementary form, via two applications of
    Cauchy-Schwarz): `(Σ f_i³)⁴ ≤ N · (Σ f_i⁴)³` for nonneg real `f`. -/
theorem Real.sum_pow_three_pow_four_le
    {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) :
    (∑ i : ι, f i ^ 3) ^ 4 ≤ (Fintype.card ι : ℝ) * (∑ i : ι, f i ^ 4) ^ 3 := by
  -- Step 1: (Σ f^3)^2 ≤ (Σ f^4)(Σ f^2) by C-S with f^2 and f.
  have h1 : (∑ i : ι, f i ^ 3) ^ 2 ≤ (∑ i : ι, f i ^ 4) * (∑ i : ι, f i ^ 2) := by
    have e1 : ∑ i : ι, f i ^ 3 = ∑ i : ι, f i ^ 2 * f i := by
      apply Finset.sum_congr rfl; intros i _; ring
    have e2 : ∑ i : ι, f i ^ 4 = ∑ i : ι, (f i ^ 2) ^ 2 := by
      apply Finset.sum_congr rfl; intros i _; ring
    rw [e1, e2]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => f i ^ 2) f
  -- Step 2: (Σ f^2)^2 ≤ N · Σ f^4 by C-S with 1 and f^2.
  have h2 : (∑ i : ι, f i ^ 2) ^ 2 ≤ (Fintype.card ι : ℝ) * (∑ i : ι, f i ^ 4) := by
    have e1 : ∑ i : ι, f i ^ 2 = ∑ i : ι, (1 : ℝ) * (f i ^ 2) := by
      apply Finset.sum_congr rfl; intros i _; ring
    have e2 : ∑ i : ι, f i ^ 4 = ∑ i : ι, (f i ^ 2) ^ 2 := by
      apply Finset.sum_congr rfl; intros i _; ring
    have eN : (Fintype.card ι : ℝ) = ∑ _i : ι, (1 : ℝ) ^ 2 := by
      simp [Finset.card_univ]
    rw [e1, e2, eN]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun i => f i ^ 2)
  -- Combine: ((Σ f^3)^2)^2 ≤ ((Σ f^4)(Σ f^2))^2 = (Σ f^4)^2 (Σ f^2)^2
  --                       ≤ (Σ f^4)^2 · N · (Σ f^4) = N · (Σ f^4)^3.
  have hsum_pos : 0 ≤ ∑ i : ι, f i ^ 4 := by
    apply Finset.sum_nonneg; intros i _
    exact pow_nonneg (hf i) 4
  have hsum2_pos : 0 ≤ ∑ i : ι, f i ^ 2 := by
    apply Finset.sum_nonneg; intros i _
    exact pow_nonneg (hf i) 2
  have hsum3_pos : 0 ≤ ∑ i : ι, f i ^ 3 := by
    apply Finset.sum_nonneg; intros i _
    exact pow_nonneg (hf i) 3
  calc (∑ i, f i ^ 3) ^ 4
      = ((∑ i, f i ^ 3) ^ 2) ^ 2 := by ring
    _ ≤ ((∑ i, f i ^ 4) * (∑ i, f i ^ 2)) ^ 2 := by
        apply pow_le_pow_left₀ (sq_nonneg _) h1
    _ = (∑ i, f i ^ 4) ^ 2 * (∑ i, f i ^ 2) ^ 2 := by ring
    _ ≤ (∑ i, f i ^ 4) ^ 2 * ((Fintype.card ι : ℝ) * (∑ i, f i ^ 4)) := by
        apply mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = (Fintype.card ι : ℝ) * (∑ i, f i ^ 4) ^ 3 := by ring

/-- **Equality case** of the second Cauchy-Schwarz step.
    If `(Σ f_i²)² = N · Σ f_i⁴` for nonneg real `f`, then all `f_i` are equal.

    Proof via the variance identity: writing `m = (Σ f²)/N`, the equality
    rearranges to `Σ (f_i² - m)² = 0`, hence each `f_i² = m`. -/
theorem Real.sum_sq_sq_eq_card_mul_sum_pow_four_imp
    {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    (hN : 0 < Fintype.card ι)
    (h : (∑ i : ι, f i ^ 2) ^ 2 = (Fintype.card ι : ℝ) * ∑ i : ι, f i ^ 4) :
    ∀ i j, f i = f j := by
  have hN_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hN
  have hN_ne : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hN_pos
  set m : ℝ := (∑ i : ι, f i ^ 2) / Fintype.card ι with hm_def
  -- From h, Σ f^4 = N m².
  have hsum4 : (∑ i : ι, f i ^ 4) = (Fintype.card ι : ℝ) * m ^ 2 := by
    have hN_sq : (Fintype.card ι : ℝ) * (∑ i : ι, f i ^ 4) = (∑ i : ι, f i ^ 2) ^ 2 :=
      h.symm
    have : m ^ 2 = (∑ i : ι, f i ^ 2) ^ 2 / (Fintype.card ι : ℝ) ^ 2 := by
      rw [hm_def]; ring
    rw [this]
    field_simp
    linarith
  -- And Σ f^2 = N m.
  have hsum2 : (∑ i : ι, f i ^ 2) = (Fintype.card ι : ℝ) * m := by
    rw [hm_def]; field_simp
  -- Compute Σ (f_i² - m)² = 0.
  have hvar : ∑ i : ι, (f i ^ 2 - m) ^ 2 = 0 := by
    have : ∑ i : ι, (f i ^ 2 - m) ^ 2 =
           (∑ i : ι, f i ^ 4) - 2 * m * (∑ i : ι, f i ^ 2)
            + (Fintype.card ι : ℝ) * m ^ 2 := by
      have hexp : ∀ i, (f i ^ 2 - m) ^ 2 = f i ^ 4 - 2 * m * f i ^ 2 + m ^ 2 := by
        intro i; ring
      simp_rw [hexp]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [show (∑ _i : ι, m ^ 2) = (Fintype.card ι : ℝ) * m ^ 2 from by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]]
      rw [show (∑ i : ι, 2 * m * f i ^ 2) = 2 * m * ∑ i : ι, f i ^ 2 from by
        rw [Finset.mul_sum]]
    rw [this, hsum4, hsum2]; ring
  -- Each (f_i² - m)² = 0, so f_i² = m.
  have hfsq : ∀ i, f i ^ 2 = m := by
    intro i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => sq_nonneg (f j ^ 2 - m))).mp hvar i (Finset.mem_univ _)
    have : f i ^ 2 - m = 0 := by
      have := pow_eq_zero_iff (two_ne_zero) |>.mp hi
      exact this
    linarith
  -- Conclude all f_i equal: f_i² = f_j² and both nonneg ⇒ f_i = f_j.
  intros i j
  have heq : f i ^ 2 = f j ^ 2 := by rw [hfsq i, hfsq j]
  exact (sq_eq_sq₀ (hf i) (hf j)).mp heq

/-- **Equality case** of the iterated Cauchy-Schwarz bound (composition).
    If `(Σ f_i³)⁴ = N · (Σ f_i⁴)³` for nonneg real `f`, then all `f_i` equal.

    Proof: trace through the same chain as `sum_pow_three_pow_four_le` and
    observe the second CS step must itself be tight. -/
theorem Real.sum_pow_three_pow_four_eq_imp
    {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    (hN : 0 < Fintype.card ι)
    (h : (∑ i : ι, f i ^ 3) ^ 4 = (Fintype.card ι : ℝ) * (∑ i : ι, f i ^ 4) ^ 3) :
    ∀ i j, f i = f j := by
  have hsum4_nn : 0 ≤ ∑ i : ι, f i ^ 4 :=
    Finset.sum_nonneg (fun i _ => pow_nonneg (hf i) 4)
  have hsum2_nn : 0 ≤ ∑ i : ι, f i ^ 2 :=
    Finset.sum_nonneg (fun i _ => pow_nonneg (hf i) 2)
  have hsum3_nn : 0 ≤ ∑ i : ι, f i ^ 3 :=
    Finset.sum_nonneg (fun i _ => pow_nonneg (hf i) 3)
  -- The first CS step: (Σ f^3)² ≤ (Σ f^4)(Σ f^2).
  have hCS1 : (∑ i : ι, f i ^ 3) ^ 2 ≤ (∑ i : ι, f i ^ 4) * (∑ i : ι, f i ^ 2) := by
    have e1 : ∑ i : ι, f i ^ 3 = ∑ i : ι, f i ^ 2 * f i := by
      apply Finset.sum_congr rfl; intros i _; ring
    have e2 : ∑ i : ι, f i ^ 4 = ∑ i : ι, (f i ^ 2) ^ 2 := by
      apply Finset.sum_congr rfl; intros i _; ring
    rw [e1, e2]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => f i ^ 2) f
  -- The second CS step: (Σ f^2)² ≤ N · Σ f^4.
  have hCS2 : (∑ i : ι, f i ^ 2) ^ 2 ≤ (Fintype.card ι : ℝ) * (∑ i : ι, f i ^ 4) := by
    have e1 : ∑ i : ι, f i ^ 2 = ∑ i : ι, (1 : ℝ) * (f i ^ 2) := by
      apply Finset.sum_congr rfl; intros i _; ring
    have e2 : ∑ i : ι, f i ^ 4 = ∑ i : ι, (f i ^ 2) ^ 2 := by
      apply Finset.sum_congr rfl; intros i _; ring
    have eN : (Fintype.card ι : ℝ) = ∑ _i : ι, (1 : ℝ) ^ 2 := by
      simp [Finset.card_univ]
    rw [e1, e2, eN]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun i => f i ^ 2)
  -- Now: equality in the composed bound forces equality in step 2 (in particular).
  -- The composed bound: (Σ f^3)^4 ≤ ((Σ f^4)(Σ f^2))² ≤ (Σ f^4)² · N · Σ f^4
  --                                = N · (Σ f^4)³
  have hcomp1 : (∑ i : ι, f i ^ 3) ^ 4 ≤ ((∑ i : ι, f i ^ 4) * (∑ i : ι, f i ^ 2)) ^ 2 := by
    rw [show ((∑ i : ι, f i ^ 3) ^ 4 : ℝ) = ((∑ i : ι, f i ^ 3) ^ 2) ^ 2 from by ring]
    exact pow_le_pow_left₀ (sq_nonneg _) hCS1 2
  have hcomp2 : ((∑ i : ι, f i ^ 4) * (∑ i : ι, f i ^ 2)) ^ 2 ≤
                (Fintype.card ι : ℝ) * (∑ i : ι, f i ^ 4) ^ 3 := by
    rw [show (((∑ i : ι, f i ^ 4) * (∑ i : ι, f i ^ 2)) ^ 2 : ℝ) =
            (∑ i : ι, f i ^ 4) ^ 2 * (∑ i : ι, f i ^ 2) ^ 2 from by ring]
    have := mul_le_mul_of_nonneg_left hCS2 (sq_nonneg (∑ i : ι, f i ^ 4))
    rw [show (Fintype.card ι : ℝ) * (∑ i : ι, f i ^ 4) ^ 3 =
            (∑ i : ι, f i ^ 4) ^ 2 * ((Fintype.card ι : ℝ) * (∑ i : ι, f i ^ 4)) from by ring]
    exact this
  -- From the composed equality + hcomp1 + hcomp2, both are equalities.
  have hcomp1_eq : (∑ i : ι, f i ^ 3) ^ 4 = ((∑ i : ι, f i ^ 4) * (∑ i : ι, f i ^ 2)) ^ 2 :=
    le_antisymm hcomp1 (h ▸ hcomp2)
  have hcomp2_eq : ((∑ i : ι, f i ^ 4) * (∑ i : ι, f i ^ 2)) ^ 2 =
                   (Fintype.card ι : ℝ) * (∑ i : ι, f i ^ 4) ^ 3 := by
    have := h ▸ hcomp1
    linarith [hcomp2]
  -- From hcomp2_eq: (Σ f^4)² ((Σ f^2)² - N · Σ f^4) = 0.
  -- Either Σ f^4 = 0 (so all f_i = 0, all equal) or (Σ f^2)² = N · Σ f^4.
  by_cases hsum4_zero : ∑ i : ι, f i ^ 4 = 0
  · -- All f_i = 0.
    have hall_zero : ∀ i, f i = 0 := by
      intro i
      have hpow := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => pow_nonneg (hf j) 4)).mp hsum4_zero i (Finset.mem_univ _)
      exact pow_eq_zero_iff (by norm_num : (4:ℕ) ≠ 0) |>.mp hpow
    intros i j; rw [hall_zero i, hall_zero j]
  · -- Reduce to (Σ f^2)² = N · Σ f^4.
    push_neg at hsum4_zero
    have hsum4_pos : 0 < ∑ i : ι, f i ^ 4 := lt_of_le_of_ne hsum4_nn (Ne.symm hsum4_zero)
    have hsum4_sq_pos : 0 < (∑ i : ι, f i ^ 4) ^ 2 := pow_pos hsum4_pos 2
    have h_step2 : (∑ i : ι, f i ^ 2) ^ 2 = (Fintype.card ι : ℝ) * (∑ i : ι, f i ^ 4) := by
      have := hcomp2_eq
      have hexp : (∑ i : ι, f i ^ 4) ^ 2 * (∑ i : ι, f i ^ 2) ^ 2 =
                  (∑ i : ι, f i ^ 4) ^ 2 * ((Fintype.card ι : ℝ) * (∑ i : ι, f i ^ 4)) := by
        nlinarith [this]
      have hcancel := mul_left_cancel₀ (ne_of_gt hsum4_sq_pos) hexp
      exact hcancel
    exact Real.sum_sq_sq_eq_card_mul_sum_pow_four_imp f hf hN h_step2

/-- For upper triangular `T`, `Σ_i ‖T_{ii}‖⁴ ≤ ‖T·T‖²_F`. -/
theorem IsUpperTriangular.sum_norm_pow_four_le
    {ι : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq ι]
    {T : Matrix ι ι ℂ} (hT : IsUpperTriangular T) :
    (∑ i : ι, ‖T i i‖ ^ 4) ≤ frobNormSq_F (T * T) := by
  have heq : ∀ i : ι, ‖T i i‖ ^ 4 = Complex.normSq (T i i) ^ 2 := by
    intro i
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.normSq_eq_norm_sq]
  rw [show (∑ i : ι, ‖T i i‖ ^ 4) = ∑ i : ι, Complex.normSq (T i i) ^ 2 from by
    apply Finset.sum_congr rfl; intros i _; exact heq i]
  exact hT.sum_diag_pow_four_le

/-- The full upper-triangular Schur trace bound:
    `‖Tr(T·T·T)‖⁴ ≤ N · (‖T·T‖²_F)³` for upper triangular `T`. -/
theorem IsUpperTriangular.norm_trace_cubed_pow_four_le
    {ι : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq ι]
    {T : Matrix ι ι ℂ} (hT : IsUpperTriangular T) :
    ‖(T * T * T).trace‖ ^ 4 ≤ (Fintype.card ι : ℝ) * frobNormSq_F (T * T) ^ 3 := by
  have hnonneg : ∀ i : ι, (0 : ℝ) ≤ ‖T i i‖ := fun _ => norm_nonneg _
  have htri := hT.norm_trace_cubed_le
  have hpw : ‖(T * T * T).trace‖ ^ 4 ≤ (∑ i : ι, ‖T i i‖ ^ 3) ^ 4 := by
    apply pow_le_pow_left₀ (norm_nonneg _) htri
  have hpm := Real.sum_pow_three_pow_four_le (fun i => ‖T i i‖) hnonneg
  have hsum := hT.sum_norm_pow_four_le
  have hcard_nn : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hsum_nn : (0 : ℝ) ≤ ∑ i : ι, ‖T i i‖ ^ 4 := by
    apply Finset.sum_nonneg; intros i _; exact pow_nonneg (norm_nonneg _) 4
  calc ‖(T * T * T).trace‖ ^ 4
      ≤ (∑ i, ‖T i i‖ ^ 3) ^ 4 := hpw
    _ ≤ (Fintype.card ι : ℝ) * (∑ i, ‖T i i‖ ^ 4) ^ 3 := hpm
    _ ≤ (Fintype.card ι : ℝ) * frobNormSq_F (T * T) ^ 3 := by
        apply mul_le_mul_of_nonneg_left _ hcard_nn
        apply pow_le_pow_left₀ hsum_nn hsum

/-! ## Towards the Schur triangulation theorem (mechanised steps)

This section progresses toward a full mechanisation of
`matrix_unitary_schur_form` via induction on dimension. The base cases
`n = 0` and `n = 1` are below. The inductive step uses
`Module.End.exists_eigenvalue` to extract an eigenvalue, an orthonormal
basis extension to build a unitary U with the eigenvector as its first
column, and then recurses on the lower-right `k × k` compression. -/

/-- For any complex matrix `A : Matrix (Fin (k+1)) (Fin (k+1)) ℂ`,
    there exist an eigenvalue `μ` and a unit vector `v : Fin (k+1) → ℂ`
    with `A *ᵥ v = μ • v`. -/
theorem Matrix.exists_unit_eigenvector {k : ℕ}
    (A : Matrix (Fin (k+1)) (Fin (k+1)) ℂ) :
    ∃ (μ : ℂ) (v : Fin (k+1) → ℂ),
      v ≠ 0 ∧ A *ᵥ v = μ • v := by
  -- Use Module.End.exists_eigenvalue on A.toLin'.
  have hNontriv : Nontrivial (Fin (k+1) → ℂ) := by
    refine ⟨0, Function.update 0 0 1, ?_⟩
    intro h
    have := congr_fun h 0
    simp at this
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (A.toLin' : (Fin (k+1) → ℂ) →ₗ[ℂ] _)
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  refine ⟨μ, v, hv.2, ?_⟩
  have happ : A.toLin' v = μ • v := hv.apply_eq_smul
  rw [Matrix.toLin'_apply] at happ
  exact happ

/-- The unitary matrix associated to an orthonormal basis `b` of
    `EuclideanSpace ℂ (Fin (k+1))`: built via Mathlib's basis change
    matrix from the standard basis. Its `j`-th column is `b j`. -/
noncomputable def schurUnitary {k : ℕ}
    (b : OrthonormalBasis (Fin (k+1)) ℂ (EuclideanSpace ℂ (Fin (k+1)))) :
    Matrix (Fin (k+1)) (Fin (k+1)) ℂ :=
  (EuclideanSpace.basisFun (Fin (k+1)) ℂ).toBasis.toMatrix b.toBasis

/-- `schurUnitary b` is unitary (`Uᴴ * U = 1`). -/
theorem schurUnitary_conjTranspose_mul_self {k : ℕ}
    (b : OrthonormalBasis (Fin (k+1)) ℂ (EuclideanSpace ℂ (Fin (k+1)))) :
    (schurUnitary b)ᴴ * schurUnitary b = 1 :=
  OrthonormalBasis.toMatrix_orthonormalBasis_conjTranspose_mul_self _ b

/-- `schurUnitary b` is unitary (`U * Uᴴ = 1`). -/
theorem schurUnitary_mul_conjTranspose_self {k : ℕ}
    (b : OrthonormalBasis (Fin (k+1)) ℂ (EuclideanSpace ℂ (Fin (k+1)))) :
    schurUnitary b * (schurUnitary b)ᴴ = 1 :=
  OrthonormalBasis.toMatrix_orthonormalBasis_self_mul_conjTranspose _ b

/-- The `(i, j)` entry of `schurUnitary b` equals `(b j) i`. -/
theorem schurUnitary_apply {k : ℕ}
    (b : OrthonormalBasis (Fin (k+1)) ℂ (EuclideanSpace ℂ (Fin (k+1))))
    (i j : Fin (k+1)) :
    schurUnitary b i j = (b j : Fin (k+1) → ℂ) i :=
  rfl

/-- Multiplying the unitary `U = schurUnitary b` against `Pi.single j 1`
    extracts column `j`, which is `b j`. -/
theorem schurUnitary_mulVec_single {k : ℕ}
    (b : OrthonormalBasis (Fin (k+1)) ℂ (EuclideanSpace ℂ (Fin (k+1))))
    (j : Fin (k+1)) :
    schurUnitary b *ᵥ Pi.single j 1 = (b j : Fin (k+1) → ℂ) := by
  ext i
  rw [Matrix.mulVec_single_one]
  simp [Matrix.col, schurUnitary_apply]

/-- Lift a `k × k` matrix to a `(k+1) × (k+1)` block-diagonal matrix
    `[[1, 0], [0, U']]` (where `1` is `1 × 1`). -/
def liftBlock {k : ℕ} (U' : Matrix (Fin k) (Fin k) ℂ) :
    Matrix (Fin (k+1)) (Fin (k+1)) ℂ :=
  fun i j =>
    Fin.cases
      (Fin.cases 1 (fun _ => 0) j)
      (fun i' => Fin.cases 0 (fun j' => U' i' j') j) i

@[simp] theorem liftBlock_zero_zero {k : ℕ} (U' : Matrix (Fin k) (Fin k) ℂ) :
    liftBlock U' 0 0 = 1 := rfl

@[simp] theorem liftBlock_zero_succ {k : ℕ} (U' : Matrix (Fin k) (Fin k) ℂ)
    (j : Fin k) : liftBlock U' 0 j.succ = 0 := rfl

@[simp] theorem liftBlock_succ_zero {k : ℕ} (U' : Matrix (Fin k) (Fin k) ℂ)
    (i : Fin k) : liftBlock U' i.succ 0 = 0 := rfl

@[simp] theorem liftBlock_succ_succ {k : ℕ} (U' : Matrix (Fin k) (Fin k) ℂ)
    (i j : Fin k) : liftBlock U' i.succ j.succ = U' i j := rfl

theorem liftBlock_conjTranspose {k : ℕ} (U' : Matrix (Fin k) (Fin k) ℂ) :
    (liftBlock U')ᴴ = liftBlock U'ᴴ := by
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
    simp [Matrix.conjTranspose_apply]

theorem liftBlock_mul_self {k : ℕ} (U' : Matrix (Fin k) (Fin k) ℂ) :
    (liftBlock U')ᴴ * liftBlock U' = liftBlock (U'ᴴ * U') := by
  ext i j
  rw [liftBlock_conjTranspose, Matrix.mul_apply]
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
  · -- (i, j) = (0, 0)
    rw [Fin.sum_univ_succ]
    simp
  · -- (i, j) = (0, succ j')
    rw [Fin.sum_univ_succ]
    simp
  · -- (i, j) = (succ i', 0)
    rw [Fin.sum_univ_succ]
    simp
  · -- (i, j) = (succ i', succ j')
    rw [Fin.sum_univ_succ]
    simp [Matrix.mul_apply]

theorem liftBlock_unitary_of_unitary {k : ℕ} {U' : Matrix (Fin k) (Fin k) ℂ}
    (hU' : U'ᴴ * U' = 1) :
    (liftBlock U')ᴴ * liftBlock U' = 1 := by
  rw [liftBlock_mul_self, hU']
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
  · simp [Matrix.one_apply]
  · simp [Matrix.one_apply, ← Fin.succ_zero_eq_one,
          (show (0 : Fin (k+1)) ≠ j'.succ from Fin.succ_ne_zero _ |>.symm)]
  · simp [Matrix.one_apply, (show i'.succ ≠ 0 from Fin.succ_ne_zero _)]
  · simp only [liftBlock_succ_succ, Matrix.one_apply, Fin.succ_inj]

theorem liftBlock_self_mul {k : ℕ} {U' : Matrix (Fin k) (Fin k) ℂ}
    (hU' : U' * U'ᴴ = 1) :
    liftBlock U' * (liftBlock U')ᴴ = 1 := by
  rw [liftBlock_conjTranspose]
  ext i j
  rw [Matrix.mul_apply]
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
  · rw [Fin.sum_univ_succ]
    simp [Matrix.one_apply]
  · rw [Fin.sum_univ_succ]
    simp [Matrix.one_apply, ← Fin.succ_zero_eq_one,
          (show (0 : Fin (k+1)) ≠ j'.succ from Fin.succ_ne_zero _ |>.symm)]
  · rw [Fin.sum_univ_succ]
    simp [Matrix.one_apply, (show i'.succ ≠ 0 from Fin.succ_ne_zero _)]
  · rw [Fin.sum_univ_succ]
    simp only [liftBlock_succ_succ, liftBlock_succ_zero, liftBlock_zero_succ,
               liftBlock_zero_zero]
    simp only [zero_mul, mul_zero, zero_add, add_zero]
    have heq := congr_fun (congr_fun hU' i') j'
    rw [Matrix.mul_apply] at heq
    by_cases hij : i' = j'
    · subst hij
      rw [Matrix.one_apply_eq] at heq
      rw [heq, Matrix.one_apply_eq]
    · have hij_succ : i'.succ ≠ j'.succ := fun h => hij (Fin.succ_inj.mp h)
      rw [Matrix.one_apply_ne hij] at heq
      rw [heq, Matrix.one_apply_ne hij_succ]

/-- Lower-right `k × k` submatrix of an `(k+1) × (k+1)` matrix. -/
def lowerRightBlock {k : ℕ} (M : Matrix (Fin (k+1)) (Fin (k+1)) ℂ) :
    Matrix (Fin k) (Fin k) ℂ :=
  fun i j => M i.succ j.succ

/-- Conjugating by `liftBlock U'`: the `(succ p', succ q')` entry
    equals `(U'ᴴ * lowerRightBlock M * U') p' q'`. -/
theorem liftBlock_conj_succ_succ_apply {k : ℕ}
    (M : Matrix (Fin (k+1)) (Fin (k+1)) ℂ) (U' : Matrix (Fin k) (Fin k) ℂ)
    (p' q' : Fin k) :
    ((liftBlock U')ᴴ * M * liftBlock U') p'.succ q'.succ =
    (U'ᴴ * lowerRightBlock M * U') p' q' := by
  -- Plan: expand both sides into double sums and compare.
  have lhs_expand : ((liftBlock U')ᴴ * M * liftBlock U') p'.succ q'.succ =
      ∑ ℓ' : Fin k, ∑ m' : Fin k,
        star (U' m' p') * M m'.succ ℓ'.succ * U' ℓ' q' := by
    rw [Matrix.mul_apply]
    rw [Fin.sum_univ_succ]
    simp only [liftBlock_zero_succ, mul_zero, zero_add]
    apply Finset.sum_congr rfl
    intros ℓ' _
    rw [Matrix.mul_apply]
    rw [Fin.sum_univ_succ]
    simp only [Matrix.conjTranspose_apply, liftBlock_succ_zero,
               liftBlock_zero_succ, star_zero,
               zero_mul, zero_add, liftBlock_succ_succ]
    rw [Finset.sum_mul]
  have rhs_expand : (U'ᴴ * lowerRightBlock M * U') p' q' =
      ∑ ℓ' : Fin k, ∑ m' : Fin k,
        star (U' m' p') * M m'.succ ℓ'.succ * U' ℓ' q' := by
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intros ℓ' _
    rw [Matrix.mul_apply]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intros m' _
    simp [Matrix.conjTranspose_apply, lowerRightBlock]
  rw [lhs_expand, rhs_expand]

/-- Conjugating by `liftBlock U'`: the `(succ p', 0)` entry is zero
    when `M` has first column `(*, 0, 0, ..., 0)`. -/
theorem liftBlock_conj_succ_zero_apply {k : ℕ}
    (M : Matrix (Fin (k+1)) (Fin (k+1)) ℂ) (U' : Matrix (Fin k) (Fin k) ℂ)
    (h_col0 : ∀ i : Fin k, M i.succ 0 = 0)
    (p' : Fin k) :
    ((liftBlock U')ᴴ * M * liftBlock U') p'.succ 0 = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intros j _
  rw [Matrix.mul_apply]
  refine Fin.cases ?_ (fun j' => ?_) j
  · -- j = 0: the term is ((liftBlock U')ᴴ * M) p'.succ 0 * 1.
    simp only [liftBlock_zero_zero, mul_one]
    rw [Fin.sum_univ_succ]
    simp only [Matrix.conjTranspose_apply, liftBlock_zero_succ, star_zero,
               zero_mul, zero_add, liftBlock_succ_succ]
    apply Finset.sum_eq_zero
    intros m _
    rw [h_col0 m]; ring
  · -- j = succ j': liftBlock U' (succ j') 0 = 0.
    simp only [liftBlock_succ_zero, mul_zero]

/-- For unitary `U = schurUnitary b` with `b 0` an eigenvector of `A`
    with eigenvalue `μ`, the first column of `Uᴴ * A * U` is
    `(μ, 0, 0, ..., 0)ᵀ`. -/
theorem schurUnitary_conjugation_first_col_apply {k : ℕ}
    (A : Matrix (Fin (k+1)) (Fin (k+1)) ℂ) (μ : ℂ)
    (b : OrthonormalBasis (Fin (k+1)) ℂ (EuclideanSpace ℂ (Fin (k+1))))
    (heigen : A *ᵥ ((b 0 : Fin (k+1) → ℂ)) = μ • ((b 0 : Fin (k+1) → ℂ)))
    (i : Fin (k+1)) :
    ((schurUnitary b)ᴴ * A * schurUnitary b) i 0 =
    if i = 0 then μ else 0 := by
  set U : Matrix (Fin (k+1)) (Fin (k+1)) ℂ := schurUnitary b with hU_def
  -- Step 1: U *ᵥ (Pi.single 0 1) = b 0 as Fin → ℂ.
  have hU_col0 : U *ᵥ Pi.single 0 1 = (b 0 : Fin (k+1) → ℂ) :=
    schurUnitary_mulVec_single b 0
  -- Step 2: Uᴴ *ᵥ (b 0) = Pi.single 0 1.
  have hUH_col0 : (Uᴴ : Matrix _ _ ℂ) *ᵥ (b 0 : Fin (k+1) → ℂ) = Pi.single 0 1 := by
    rw [← hU_col0, Matrix.mulVec_mulVec, schurUnitary_conjTranspose_mul_self,
        Matrix.one_mulVec]
  -- Step 3: column 0 of Uᴴ A U is μ • Pi.single 0 1.
  have h_col : (Uᴴ * A * U : Matrix _ _ ℂ) *ᵥ Pi.single 0 1 =
               (μ • (Pi.single 0 1 : Fin (k+1) → ℂ)) := by
    rw [show (Uᴴ * A * U : Matrix _ _ ℂ) *ᵥ (Pi.single 0 1 : Fin (k+1) → ℂ) =
        Uᴴ *ᵥ (A *ᵥ (U *ᵥ (Pi.single 0 1 : Fin (k+1) → ℂ))) by
          rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]]
    rw [hU_col0, heigen]
    rw [Matrix.mulVec_smul]
    rw [hUH_col0]
  -- Step 4: extract i-th component.
  have hi : ((Uᴴ * A * U : Matrix _ _ ℂ) *ᵥ Pi.single 0 1) i = (Uᴴ * A * U) i 0 := by
    rw [Matrix.mulVec_single_one]; rfl
  rw [← hi, h_col]
  by_cases hi0 : i = 0
  · subst hi0; simp [Pi.single]
  · rw [Pi.smul_apply, Pi.single_eq_of_ne hi0, smul_zero, if_neg hi0]

/-- For any nonzero `v : EuclideanSpace ℂ (Fin (k+1))`, there exists an
    orthonormal basis `b : OrthonormalBasis (Fin (k+1)) ℂ (EuclideanSpace ℂ (Fin (k+1)))`
    with `b 0 = v / ‖v‖` (a unit vector pointing along `v`). -/
theorem exists_orthonormalBasis_first_eq {k : ℕ}
    (v : EuclideanSpace ℂ (Fin (k+1))) (hv : v ≠ 0) :
    ∃ b : OrthonormalBasis (Fin (k+1)) ℂ (EuclideanSpace ℂ (Fin (k+1))),
      b 0 = (‖v‖⁻¹ : ℂ) • v := by
  -- Define v_ext : Fin (k+1) → E with v_ext 0 = (‖v‖⁻¹ : ℂ) • v, others 0.
  let v_ext : Fin (k+1) → EuclideanSpace ℂ (Fin (k+1)) :=
    fun i => if i = 0 then (‖v‖⁻¹ : ℂ) • v else 0
  -- The set s = {0}.
  let s : Set (Fin (k+1)) := {0}
  -- The restriction s.restrict v_ext : s → E is orthonormal (single unit vector).
  have hvnorm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hvnorm_ne : (‖v‖ : ℂ) ≠ 0 := by
    rw [show ((‖v‖ : ℂ)) = ((‖v‖ : ℝ) : ℂ) from rfl]
    exact_mod_cast ne_of_gt hvnorm_pos
  have hv_ext_zero_norm : ‖((‖v‖⁻¹ : ℂ) • v : EuclideanSpace ℂ (Fin (k+1)))‖ = 1 := by
    rw [norm_smul]
    have habs : ‖(‖v‖⁻¹ : ℂ)‖ = ‖v‖⁻¹ := by
      simp [norm_inv, Complex.norm_real]
    rw [habs]
    field_simp
  have hortho : Orthonormal ℂ (s.restrict v_ext) := by
    rw [orthonormal_iff_ite]
    rintro i j
    have hi : i.val = 0 := i.property
    have hj : j.val = 0 := j.property
    have hij_eq : i = j := Subtype.ext (hi.trans hj.symm)
    rw [hij_eq, if_pos rfl]
    have hv_ext_eq : v_ext j.val = (‖v‖⁻¹ : ℂ) • v := by
      rw [hj]; simp [v_ext]
    show inner ℂ (v_ext j.val) (v_ext j.val) = 1
    rw [hv_ext_eq, inner_self_eq_norm_sq_to_K, hv_ext_zero_norm]
    push_cast; ring
  have hcard : Module.finrank ℂ (EuclideanSpace ℂ (Fin (k+1))) = Fintype.card (Fin (k+1)) :=
    finrank_euclideanSpace
  obtain ⟨b, hb⟩ := hortho.exists_orthonormalBasis_extension_of_card_eq hcard
  refine ⟨b, ?_⟩
  have h0 : (0 : Fin (k+1)) ∈ s := rfl
  have := hb 0 h0
  rw [show v_ext 0 = (‖v‖⁻¹ : ℂ) • v from by simp [v_ext]] at this
  exact this

/-- Schur form for the `0 × 0` matrix: any `U` works (vacuously upper
    triangular, and the identity is trivially unitary). -/
theorem matrix_unitary_schur_form_zero (A : Matrix (Fin 0) (Fin 0) ℂ) :
    ∃ U : Matrix (Fin 0) (Fin 0) ℂ,
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ IsUpperTriangular (Uᴴ * A * U) := by
  refine ⟨1, ?_, ?_, ?_⟩
  · simp
  · simp
  · intros i _ _; exact i.elim0

/-- Schur form for the `1 × 1` matrix: `U = 1` works (the matrix is
    upper triangular trivially, since there is no strictly-below-diagonal
    entry). -/
theorem matrix_unitary_schur_form_one (A : Matrix (Fin 1) (Fin 1) ℂ) :
    ∃ U : Matrix (Fin 1) (Fin 1) ℂ,
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ IsUpperTriangular (Uᴴ * A * U) := by
  refine ⟨1, ?_, ?_, ?_⟩
  · simp
  · simp
  · intros i j hij
    -- Fin 1 has only one element, so j < i is impossible.
    have : i = j := Subsingleton.elim i j
    rw [this] at hij
    exact absurd hij (lt_irrefl _)

/-! ## Schur triangulation: inductive step -/

/-- The inductive step of the Schur triangulation: from the IH on
    dimension `k`, derive Schur form for dimension `k + 1`. -/
theorem matrix_unitary_schur_form_succ {k : ℕ}
    (ih : ∀ B : Matrix (Fin k) (Fin k) ℂ,
      ∃ U' : Matrix (Fin k) (Fin k) ℂ,
        U'ᴴ * U' = 1 ∧ U' * U'ᴴ = 1 ∧ IsUpperTriangular (U'ᴴ * B * U'))
    (A : Matrix (Fin (k+1)) (Fin (k+1)) ℂ) :
    ∃ U : Matrix (Fin (k+1)) (Fin (k+1)) ℂ,
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ IsUpperTriangular (Uᴴ * A * U) := by
  obtain ⟨μ, v, hv_ne, heigen⟩ := Matrix.exists_unit_eigenvector A
  have v_eu_ne : ((WithLp.equiv 2 _).symm v : EuclideanSpace ℂ (Fin (k+1))) ≠ 0 := by
    intro h
    apply hv_ne
    have := congr_arg (WithLp.equiv 2 _) h
    simpa using this
  obtain ⟨b, hb_eq⟩ := exists_orthonormalBasis_first_eq
    ((WithLp.equiv 2 _).symm v : EuclideanSpace ℂ (Fin (k+1))) v_eu_ne
  set U₁ := schurUnitary b with hU₁_def
  have h_eigen_b0 : A *ᵥ ((b 0 : Fin (k+1) → ℂ)) = μ • ((b 0 : Fin (k+1) → ℂ)) := by
    rw [hb_eq]
    set c : ℂ := (‖((WithLp.equiv 2 _).symm v : EuclideanSpace ℂ (Fin (k+1)))‖⁻¹ : ℂ)
    have hcoerce : ((c • ((WithLp.equiv 2 _).symm v : EuclideanSpace ℂ (Fin (k+1))) :
                   EuclideanSpace ℂ (Fin (k+1))) : Fin (k+1) → ℂ) = c • v := by
      ext i
      simp [WithLp.equiv]
    rw [hcoerce]
    rw [Matrix.mulVec_smul, heigen, smul_comm]
  set M := U₁ᴴ * A * U₁
  have h_first_col : ∀ i : Fin (k+1), M i 0 = if i = 0 then μ else 0 :=
    fun i => schurUnitary_conjugation_first_col_apply A μ b h_eigen_b0 i
  obtain ⟨U', hU'L, hU'R, hU'Tri⟩ := ih (lowerRightBlock M)
  set U_full := liftBlock U'
  refine ⟨U₁ * U_full, ?_, ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul]
    rw [show U_fullᴴ * U₁ᴴ * (U₁ * U_full) = U_fullᴴ * (U₁ᴴ * U₁) * U_full by
      simp only [Matrix.mul_assoc]]
    rw [schurUnitary_conjTranspose_mul_self, Matrix.mul_one]
    exact liftBlock_unitary_of_unitary hU'L
  · rw [Matrix.conjTranspose_mul]
    rw [show U₁ * U_full * (U_fullᴴ * U₁ᴴ) = U₁ * (U_full * U_fullᴴ) * U₁ᴴ by
      simp only [Matrix.mul_assoc]]
    rw [liftBlock_self_mul hU'R, Matrix.mul_one]
    exact schurUnitary_mul_conjTranspose_self b
  · rw [Matrix.conjTranspose_mul]
    rw [show U_fullᴴ * U₁ᴴ * A * (U₁ * U_full) = U_fullᴴ * (U₁ᴴ * A * U₁) * U_full by
      simp only [Matrix.mul_assoc]]
    intro p q hqp
    induction p using Fin.cases with
    | zero => exact absurd hqp (Fin.not_lt_zero q)
    | succ p' =>
      induction q using Fin.cases with
      | zero =>
        apply liftBlock_conj_succ_zero_apply
        intros i
        have := h_first_col i.succ
        rw [if_neg (Fin.succ_ne_zero _)] at this
        exact this
      | succ q' =>
        rw [liftBlock_conj_succ_succ_apply]
        apply hU'Tri
        exact Fin.succ_lt_succ_iff.mp hqp

/-- **Strong inductive form of `matrix_unitary_schur_form`.**
    For every natural number `m` and every complex `m × m` matrix,
    Schur triangulation holds. -/
theorem matrix_unitary_schur_form_proved : ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ),
    ∃ U : Matrix (Fin m) (Fin m) ℂ,
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ IsUpperTriangular (Uᴴ * A * U) := by
  intro m
  induction m with
  | zero => exact matrix_unitary_schur_form_zero
  | succ k ih => exact matrix_unitary_schur_form_succ ih

/-- **Unitary Schur triangulation (proved theorem).** For any complex
    `n × n` matrix `A`, there exists a unitary basis change `U` such
    that `Uᴴ · A · U` is upper triangular. Replaces the previous axiom
    of the same name; mechanised end-to-end by induction on `n` via
    `matrix_unitary_schur_form_proved`. -/
theorem matrix_unitary_schur_form (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ,
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ IsUpperTriangular (Uᴴ * A * U) :=
  matrix_unitary_schur_form_proved n A

/-! ## Composition support: cube roots of unity don't pair to zero -/

/-- No two cube roots of `1 : ℂ` sum to zero. The cube roots of unity are
    `{1, ω, ω²}` where `ω = e^{2πi/3}`; their pairwise sums are
    `2, 1 + ω, 1 + ω², 2ω, ω + ω² = -1, 2ω²`, all nonzero.

    Proof: if `z + w = 0` then `w = -z`, so `w³ = -z³ = -1`, contradicting
    `w³ = 1`. -/
theorem cube_root_one_add_ne_zero {z w : ℂ}
    (hz : z ^ 3 = 1) (hw : w ^ 3 = 1) : z + w ≠ 0 := by
  intro h
  have hw_eq : w = -z := by linear_combination h
  have h_neg_z_cubed : (-z) ^ 3 = -(z ^ 3) := by ring
  rw [hw_eq, h_neg_z_cubed, hz] at hw
  have hcontra : ((2 : ℂ) = 0) := by linear_combination -hw
  exact absurd hcontra (by norm_num)

/-- For upper triangular `T : Matrix (Fin N) (Fin N) ℂ` with `(T·T)`
    having zero strictly-above-diagonal entries and each diagonal entry
    `T_{ii}` a cube root of unity, `T` is itself diagonal.

    The proof is strong induction on `j.val - i.val`. For each `i < j`,
    decompose `(T·T)_{ij} = T_{i,i} T_{i,j} + T_{i,j} T_{j,j} + (cross)`,
    where the cross term `Σ_{k ∈ univ.erase i.erase j} T_{i,k} T_{k,j}`
    vanishes (`k < i` or `k > j` by upper-triangular; `i < k < j` by IH).
    Then `T_{i,j}(T_{ii} + T_{j,j}) = 0` and `T_{ii} + T_{j,j} ≠ 0`
    forces `T_{i,j} = 0`. -/
theorem IsUpperTriangular.diagonal_of_sq_offdiag_zero_of_diag_pow_three_one
    {N : ℕ} {T : Matrix (Fin N) (Fin N) ℂ}
    (hT : IsUpperTriangular T)
    (hT2_offdiag : ∀ i j : Fin N, i < j → (T * T) i j = 0)
    (hT3 : ∀ i : Fin N, (T i i) ^ 3 = 1) :
    ∀ i j : Fin N, i < j → T i j = 0 := by
  suffices ∀ d : ℕ, ∀ i j : Fin N, i < j → j.val - i.val ≤ d → T i j = 0 by
    intros i j hij; exact this (j.val - i.val) i j hij (le_refl _)
  intro d
  induction d using Nat.strong_induction_on with
  | _ d IH =>
    intros i j hij hd
    have hTTij : (T * T) i j = 0 := hT2_offdiag i j hij
    rw [Matrix.mul_apply] at hTTij
    have hi_mem : i ∈ (Finset.univ : Finset (Fin N)) := Finset.mem_univ _
    have hj_mem_erase : j ∈ Finset.univ.erase i :=
      Finset.mem_erase.mpr ⟨(ne_of_lt hij).symm, Finset.mem_univ j⟩
    have step1 : (∑ k : Fin N, T i k * T k j) =
                 T i i * T i j + ∑ k ∈ Finset.univ.erase i, T i k * T k j := by
      rw [← Finset.add_sum_erase _ _ hi_mem]
    have step2 : ∑ k ∈ Finset.univ.erase i, T i k * T k j =
                 T i j * T j j +
                 ∑ k ∈ (Finset.univ.erase i).erase j, T i k * T k j := by
      rw [← Finset.add_sum_erase _ _ hj_mem_erase]
    have step3 :
        ∑ k ∈ (Finset.univ.erase i).erase j, T i k * T k j = 0 := by
      apply Finset.sum_eq_zero
      intros k hk
      have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
      have hki : k ≠ i := by
        have hk_in_erase_i : k ∈ Finset.univ.erase i :=
          (Finset.mem_erase.mp hk).2
        exact (Finset.mem_erase.mp hk_in_erase_i).1
      rcases lt_trichotomy k i with hlt | heq | hgt
      · rw [hT i k hlt]; ring
      · exact absurd heq hki
      · rcases lt_trichotomy k j with hlt' | heq' | hgt'
        · -- i < k < j: apply IH.
          have hki_diff : k.val - i.val < d := by
            have h1 : k.val < j.val := hlt'
            have h2 : i.val < k.val := hgt
            have h3 : j.val - i.val ≤ d := hd
            omega
          have hT_ik := IH (k.val - i.val) hki_diff i k hgt (le_refl _)
          rw [hT_ik]; ring
        · exact absurd heq' hkj
        · -- k > j: T_kj = 0 from upper triangular.
          rw [hT k j hgt']; ring
    rw [step1, step2, step3, add_zero] at hTTij
    -- hTTij : T_ii * T_ij + T_ij * T_jj = 0
    -- Equivalently: T_ij * (T_ii + T_jj) = 0.
    have hfactored : T i j * (T i i + T j j) = 0 := by linear_combination hTTij
    have hsum_ne_zero : T i i + T j j ≠ 0 :=
      cube_root_one_add_ne_zero (hT3 i) (hT3 j)
    rcases mul_eq_zero.mp hfactored with h | h
    · exact h
    · exact absurd h hsum_ne_zero

/-- **Composition lemma**: from the chain equality
    `‖Tr(T³)‖⁴ = N (‖T·T‖²_F)³` plus `Tr(T³) = (N : ℂ)` (positive real)
    plus `T` upper triangular plus `N > 0`,
    derive that each diagonal entry `T_{ii}³ = 1` and `T` is diagonal. -/
theorem IsUpperTriangular.diagonal_of_chain_eq_at_real_pos
    {N : ℕ} {T : Matrix (Fin N) (Fin N) ℂ}
    (hT : IsUpperTriangular T)
    (hN : 0 < N)
    (hTrEq : (T * T * T).trace = (N : ℂ))
    (h_chain_eq : ‖(T * T * T).trace‖ ^ 4 =
                  (N : ℝ) * frobNormSq_F (T * T) ^ 3) :
    (∀ i : Fin N, (T i i) ^ 3 = 1) ∧ (∀ i j : Fin N, i ≠ j → T i j = 0) := by
  -- LHS = ‖N‖^4 = N^4 (since N is a nonneg natural cast to ℂ).
  have hLHS : ‖(T * T * T).trace‖ ^ 4 = (N : ℝ) ^ 4 := by
    rw [hTrEq]
    simp [Complex.norm_natCast]
  -- So N^4 = N * (frobNormSq_F (T*T))^3, i.e., N^3 = (frobNormSq_F (T*T))^3.
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_pos
  have hTT_F : frobNormSq_F (T * T) = (N : ℝ) := by
    have hcube : (N : ℝ) ^ 3 = frobNormSq_F (T * T) ^ 3 := by
      have h1 : (N : ℝ) ^ 4 = (N : ℝ) * frobNormSq_F (T * T) ^ 3 := by
        rw [← hLHS]; exact h_chain_eq
      have h2 : (N : ℝ) * (N : ℝ) ^ 3 = (N : ℝ) * frobNormSq_F (T * T) ^ 3 := by
        rw [show (N : ℝ) * (N : ℝ) ^ 3 = (N : ℝ) ^ 4 from by ring]; exact h1
      exact mul_left_cancel₀ hN_ne h2
    have hF_nn : 0 ≤ frobNormSq_F (T * T) := frobNormSq_F_nonneg _
    have hN_nn : (0 : ℝ) ≤ N := le_of_lt hN_pos
    -- a^3 = b^3 with a, b nonneg ⇒ a = b.
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · -- h : frobNormSq_F (T*T) < N. Then frobNormSq_F^3 < N^3, contradicting hcube.
      have h3lt : frobNormSq_F (T * T) ^ 3 < (N : ℝ) ^ 3 :=
        pow_lt_pow_left₀ h hF_nn (by norm_num)
      linarith
    · -- h : frobNormSq_F (T*T) > N. Then N^3 < frobNormSq_F^3, contradicting hcube.
      have h3lt : (N : ℝ) ^ 3 < frobNormSq_F (T * T) ^ 3 :=
        pow_lt_pow_left₀ h hN_nn (by norm_num)
      linarith
  -- Now extract each link in the chain.
  -- Using the inequality chain proof:
  -- ‖Tr(T^3)‖^4 ≤ (Σ ‖T_ii‖^3)^4 ≤ N (Σ ‖T_ii‖^4)^3 ≤ N (frobNormSq_F (T*T))^3.
  -- Each link is ≤; bookend equality forces each = .
  have h_sum3_nn : 0 ≤ ∑ i : Fin N, ‖T i i‖ ^ 3 :=
    Finset.sum_nonneg (fun i _ => pow_nonneg (norm_nonneg _) 3)
  have h_sum4_nn : 0 ≤ ∑ i : Fin N, ‖T i i‖ ^ 4 :=
    Finset.sum_nonneg (fun i _ => pow_nonneg (norm_nonneg _) 4)
  have hN_card : Fintype.card (Fin N) = N := Fintype.card_fin N
  have hN_card_real : (Fintype.card (Fin N) : ℝ) = N := by simp [hN_card]
  -- Link 1: triangle: ‖Tr(T^3)‖ ≤ Σ ‖T_ii‖^3.
  have hL1 : ‖(T * T * T).trace‖ ≤ ∑ i : Fin N, ‖T i i‖ ^ 3 :=
    hT.norm_trace_cubed_le
  -- Link 2: iterated CS: (Σ ‖T_ii‖^3)^4 ≤ N (Σ ‖T_ii‖^4)^3.
  have hL2 : (∑ i : Fin N, ‖T i i‖ ^ 3) ^ 4 ≤
             (Fintype.card (Fin N) : ℝ) * (∑ i : Fin N, ‖T i i‖ ^ 4) ^ 3 :=
    Real.sum_pow_three_pow_four_le _ (fun _ => norm_nonneg _)
  -- Link 3: Schur tightness on T·T: Σ ‖T_ii‖^4 ≤ frobNormSq_F (T*T).
  have hL3 : ∑ i : Fin N, ‖T i i‖ ^ 4 ≤ frobNormSq_F (T * T) :=
    hT.sum_norm_pow_four_le
  -- Bookend: ‖Tr(T^3)‖^4 = N (frobNormSq_F (T*T))^3.
  -- Squeeze each equal.
  have hL1_eq : ‖(T * T * T).trace‖ = ∑ i : Fin N, ‖T i i‖ ^ 3 := by
    -- ‖Tr(T^3)‖^4 ≤ (Σ ‖T_ii‖^3)^4 ≤ ... = ‖Tr(T^3)‖^4. So all =.
    have htrace_pow : ‖(T * T * T).trace‖ ^ 4 ≤ (∑ i : Fin N, ‖T i i‖ ^ 3) ^ 4 :=
      pow_le_pow_left₀ (norm_nonneg _) hL1 4
    have hL2L3 : (∑ i : Fin N, ‖T i i‖ ^ 3) ^ 4 ≤ (N : ℝ) * frobNormSq_F (T * T) ^ 3 := by
      calc (∑ i : Fin N, ‖T i i‖ ^ 3) ^ 4
          ≤ (Fintype.card (Fin N) : ℝ) * (∑ i : Fin N, ‖T i i‖ ^ 4) ^ 3 := hL2
        _ = (N : ℝ) * (∑ i : Fin N, ‖T i i‖ ^ 4) ^ 3 := by rw [hN_card_real]
        _ ≤ (N : ℝ) * frobNormSq_F (T * T) ^ 3 := by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt hN_pos)
            exact pow_le_pow_left₀ h_sum4_nn hL3 3
    have h_pow_eq : ‖(T * T * T).trace‖ ^ 4 = (∑ i : Fin N, ‖T i i‖ ^ 3) ^ 4 := by
      linarith
    -- Both nonneg, take 4th root: ‖Tr‖ = Σ.
    have h_lhs_nn : (0 : ℝ) ≤ ‖(T * T * T).trace‖ := norm_nonneg _
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have : ‖(T * T * T).trace‖ ^ 4 < (∑ i : Fin N, ‖T i i‖ ^ 3) ^ 4 :=
        pow_lt_pow_left₀ h h_lhs_nn (by norm_num)
      linarith
    · have : (∑ i : Fin N, ‖T i i‖ ^ 3) ^ 4 < ‖(T * T * T).trace‖ ^ 4 :=
        pow_lt_pow_left₀ h h_sum3_nn (by norm_num)
      linarith
  have hL3_eq : ∑ i : Fin N, ‖T i i‖ ^ 4 = frobNormSq_F (T * T) := by
    -- Similarly: from h_chain_eq + hL1_eq, the remaining chain
    -- (Σ ‖T_ii‖^3)^4 ≤ N (Σ ‖T_ii‖^4)^3 ≤ N (frobNormSq_F (T*T))^3 must be tight,
    -- hence Σ ‖T_ii‖^4 = frobNormSq_F (T*T).
    have hlink23 : (∑ i : Fin N, ‖T i i‖ ^ 3) ^ 4 = (N : ℝ) * frobNormSq_F (T * T) ^ 3 := by
      have : ‖(T * T * T).trace‖ ^ 4 = (∑ i : Fin N, ‖T i i‖ ^ 3) ^ 4 := by
        rw [hL1_eq]
      linarith [h_chain_eq]
    -- Now from (Σ ‖T_ii‖^3)^4 ≤ N (Σ ‖T_ii‖^4)^3 ≤ N (frobNormSq_F (T*T))^3 = (Σ ‖T_ii‖^3)^4,
    -- we get Σ ‖T_ii‖^4 = frobNormSq_F (T*T).
    have h_squeeze1 : (Fintype.card (Fin N) : ℝ) * (∑ i : Fin N, ‖T i i‖ ^ 4) ^ 3 ≤
        (N : ℝ) * frobNormSq_F (T * T) ^ 3 := by
      rw [hN_card_real]
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hN_pos)
      exact pow_le_pow_left₀ h_sum4_nn hL3 3
    have h_squeeze2 : (Fintype.card (Fin N) : ℝ) * (∑ i : Fin N, ‖T i i‖ ^ 4) ^ 3 ≥
        (∑ i : Fin N, ‖T i i‖ ^ 3) ^ 4 := hL2
    have h_card_eq : (Fintype.card (Fin N) : ℝ) * (∑ i : Fin N, ‖T i i‖ ^ 4) ^ 3 =
        (N : ℝ) * frobNormSq_F (T * T) ^ 3 := by
      have hgt : (N : ℝ) * (∑ i : Fin N, ‖T i i‖ ^ 4) ^ 3 ≥ (∑ i : Fin N, ‖T i i‖ ^ 3) ^ 4 := by
        rw [← hN_card_real]; exact h_squeeze2
      linarith [h_squeeze1, hgt]
    have h_inner_eq : (∑ i : Fin N, ‖T i i‖ ^ 4) ^ 3 = frobNormSq_F (T * T) ^ 3 := by
      rw [hN_card_real] at h_card_eq
      exact mul_left_cancel₀ hN_ne h_card_eq
    have hF_nn : 0 ≤ frobNormSq_F (T * T) := frobNormSq_F_nonneg _
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have : (∑ i : Fin N, ‖T i i‖ ^ 4) ^ 3 < frobNormSq_F (T * T) ^ 3 :=
        pow_lt_pow_left₀ h h_sum4_nn (by norm_num)
      linarith
    · have : frobNormSq_F (T * T) ^ 3 < (∑ i : Fin N, ‖T i i‖ ^ 4) ^ 3 :=
        pow_lt_pow_left₀ h hF_nn (by norm_num)
      linarith
  -- Now apply equality lemmas.
  -- (i) Schur tightness: T*T off-diagonals vanish.
  have hT2_offdiag : ∀ i j : Fin N, i ≠ j → (T * T) i j = 0 := by
    have hh : ∀ i, ‖T i i‖ ^ 4 = Complex.normSq (T i i) ^ 2 := by
      intro i
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.normSq_eq_norm_sq]
    have hh_TT : ∀ i, Complex.normSq (T i i) ^ 2 = Complex.normSq ((T * T) i i) := by
      intro i; rw [hT.diag_mul_self i, map_pow]
    have h_diag_eq_F : ∑ i : Fin N, Complex.normSq ((T * T) i i) = frobNormSq_F (T * T) := by
      rw [← hL3_eq]
      apply Finset.sum_congr rfl
      intros i _
      rw [hh i, hh_TT i]
    exact (frobNormSq_F_eq_sum_diag_iff (T * T)).mp h_diag_eq_F
  -- (ii) CS iterated: all ‖T_ii‖ equal.
  have hL2_eq : (∑ i : Fin N, ‖T i i‖ ^ 3) ^ 4 =
                (Fintype.card (Fin N) : ℝ) * (∑ i : Fin N, ‖T i i‖ ^ 4) ^ 3 := by
    rw [hN_card_real]
    have : (∑ i : Fin N, ‖T i i‖ ^ 3) ^ 4 ≤ (N : ℝ) * (∑ i : Fin N, ‖T i i‖ ^ 4) ^ 3 := by
      rw [← hN_card_real]; exact hL2
    have : (N : ℝ) * (∑ i : Fin N, ‖T i i‖ ^ 4) ^ 3 ≤ (N : ℝ) * frobNormSq_F (T * T) ^ 3 := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hN_pos)
      exact pow_le_pow_left₀ h_sum4_nn hL3 3
    have h_mid : (N : ℝ) * (∑ i : Fin N, ‖T i i‖ ^ 4) ^ 3 = (N : ℝ) * frobNormSq_F (T * T) ^ 3 := by
      rw [hL3_eq]
    have h_lhs_eq : (∑ i : Fin N, ‖T i i‖ ^ 3) ^ 4 = (N : ℝ) * frobNormSq_F (T * T) ^ 3 := by
      rw [← hL1_eq]; exact h_chain_eq
    linarith
  have h_norms_const : ∀ i j : Fin N, ‖T i i‖ = ‖T j j‖ := by
    apply Real.sum_pow_three_pow_four_eq_imp _ (fun _ => norm_nonneg _)
    · rw [hN_card]; exact hN
    · exact hL2_eq
  -- (iii) Triangle: each T_ii^3 nonneg real.
  have hL1_eq_re : ∑ i : Fin N, ‖T i i‖ ^ 3 = ((T * T * T).trace).re := by
    -- ‖Tr(T^3)‖ = Σ ‖T_ii‖^3 by hL1_eq.
    -- And Tr(T^3) = N (positive real), so ‖Tr(T^3)‖ = N = (Tr(T^3)).re.
    rw [← hL1_eq, hTrEq]
    simp [Complex.norm_natCast]
  -- We need `Σ ‖T_ii^3‖ = (Σ T_ii^3).re`. Use trace_mul_self_mul_self.
  have h_tr_split : (T * T * T).trace = ∑ i : Fin N, (T i i) ^ 3 :=
    hT.trace_mul_self_mul_self
  have h_norm_sum_cubed : ∑ i : Fin N, ‖(T i i) ^ 3‖ = (∑ i : Fin N, (T i i) ^ 3).re := by
    have h_abs_eq : ∀ i : Fin N, ‖(T i i) ^ 3‖ = ‖T i i‖ ^ 3 := fun i => by rw [norm_pow]
    simp_rw [h_abs_eq]
    rw [hL1_eq_re, h_tr_split]
  have h_each_nn_real : ∀ i, ((T i i) ^ 3).im = 0 ∧ 0 ≤ ((T i i) ^ 3).re := by
    have := norm_sum_eq_re_sum_imp_each_nonneg_real
              (z := fun i : Fin N => (T i i) ^ 3) h_norm_sum_cubed
    exact this
  -- Now combine: each T_ii^3 nonneg real, all ‖T_ii‖ equal to some r.
  -- Total: Σ T_ii^3 = N (real), so N r^3 = N (where r = ‖T_ii‖).
  -- So r = 1, each T_ii^3 = r^3 = 1.
  have h_T_ii_norm : ∀ i, ‖T i i‖ = 1 := by
    -- All ‖T_ii‖ equal to some r. Σ ‖T_ii‖^3 = N (from hL1_eq_re and Tr(T^3) = N).
    -- So r^3 · N = N, r = 1.
    intro i
    -- All equal: take r = ‖T i0 i0‖ for some i0 : Fin N (exists since hN : 0 < N).
    haveI : NeZero N := ⟨Nat.pos_iff_ne_zero.mp hN⟩
    let i0 : Fin N := ⟨0, hN⟩
    let r := ‖T i0 i0‖
    have hr_eq : ∀ j, ‖T j j‖ = r := fun j => h_norms_const j i0
    have hsum3_eq : ∑ j : Fin N, ‖T j j‖ ^ 3 = (N : ℝ) * r ^ 3 := by
      simp_rw [hr_eq]
      rw [Finset.sum_const, Finset.card_univ, hN_card, nsmul_eq_mul]
    have h_total : (N : ℝ) * r ^ 3 = (N : ℝ) := by
      rw [← hsum3_eq, hL1_eq_re, hTrEq]; simp
    have hr_cubed : r ^ 3 = 1 := mul_left_cancel₀ hN_ne (by rw [h_total]; ring)
    have hr_nn : 0 ≤ r := norm_nonneg _
    have hr_one : r = 1 := by
      -- r^3 = 1 with r ≥ 0 ⇒ r = 1 (cube root injective on [0, ∞)).
      nlinarith [hr_cubed, sq_nonneg (r - 1), sq_nonneg r, hr_nn]
    rw [hr_eq i, hr_one]
  have h_T_ii_pow_three : ∀ i, (T i i) ^ 3 = 1 := by
    intro i
    have hnn := h_each_nn_real i
    have hnorm : ‖(T i i) ^ 3‖ = 1 := by rw [norm_pow, h_T_ii_norm i]; ring
    have h_normSq : Complex.normSq ((T i i) ^ 3) = 1 := by
      rw [Complex.normSq_eq_norm_sq, hnorm]; ring
    have h_normSq_eq : ((T i i) ^ 3).re ^ 2 + ((T i i) ^ 3).im ^ 2 = 1 := by
      have := h_normSq
      rw [Complex.normSq_apply] at this
      linarith [this, sq (((T i i) ^ 3).re), sq (((T i i) ^ 3).im)]
    have h_re_one : ((T i i) ^ 3).re = 1 := by
      rw [hnn.1] at h_normSq_eq
      have hsq : ((T i i) ^ 3).re ^ 2 = 1 := by linarith
      have habs : |((T i i) ^ 3).re| = 1 := by
        rw [← Real.sqrt_sq_eq_abs, hsq, Real.sqrt_one]
      rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1) |>.mp habs with h | h
      · exact h
      · exfalso; linarith [hnn.2]
    apply Complex.ext
    · rw [h_re_one]; simp
    · rw [hnn.1]; simp
  -- Now apply diagonal lemma.
  have h_diag : ∀ i j : Fin N, i ≠ j → T i j = 0 := by
    intros i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hT.diagonal_of_sq_offdiag_zero_of_diag_pow_three_one
        (fun a b hab => hT2_offdiag a b (ne_of_lt hab)) h_T_ii_pow_three i j h
    · -- i > j, but T upper triangular, so T i j = 0 directly.
      exact hT i j h
  exact ⟨h_T_ii_pow_three, h_diag⟩

/-- For `T` diagonal with each diagonal entry a cube root of unity,
    `T · Tᴴ = 1`. Entry-wise computation: only the `k = i` term in
    `Σ_k T_{i,k} · star (T_{j,k})` survives, and at `i = j` it equals
    `|T_{ii}|² = 1` (since `|T_{ii}|³ = |1| = 1`); at `i ≠ j` it
    contains `star (T_{j,i}) = 0`. -/
theorem isDiagonal_pow_three_one_mul_conjTranspose_eq_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] {T : Matrix ι ι ℂ}
    (h_diag : ∀ i j : ι, i ≠ j → T i j = 0)
    (h_pow_three : ∀ i : ι, (T i i) ^ 3 = 1) :
    T * Tᴴ = 1 := by
  -- Each |T_ii| = 1 from |T_ii|³ = 1 (since normSq is real nonneg).
  have h_normSq_one : ∀ i : ι, Complex.normSq (T i i) = 1 := by
    intro i
    have hnn : (0 : ℝ) ≤ Complex.normSq (T i i) := Complex.normSq_nonneg _
    have h3 : Complex.normSq (T i i) ^ 3 = 1 := by
      have : Complex.normSq ((T i i) ^ 3) = Complex.normSq (1 : ℂ) := by
        rw [h_pow_three i]
      rw [map_pow, Complex.normSq_one] at this
      exact this
    nlinarith [hnn, h3, sq_nonneg (Complex.normSq (T i i) - 1),
               sq_nonneg (Complex.normSq (T i i) + 1)]
  -- Now compute (T * Tᴴ) entry-wise.
  ext i j
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single i ?_ ?_]
  · -- Term at k = i: T i i * star (T j i).
    rw [Matrix.conjTranspose_apply]
    by_cases hij : i = j
    · -- i = j: T i i * star (T i i) = |T_ii|² = 1.
      subst hij
      rw [Matrix.one_apply, if_pos rfl]
      have h_mul_star : T i i * star (T i i) = (Complex.normSq (T i i) : ℂ) := by
        rw [show (star (T i i) : ℂ) = (starRingEnd ℂ) (T i i) from rfl, mul_comm]
        exact Complex.normSq_eq_conj_mul_self.symm
      rw [h_mul_star, h_normSq_one i]; simp
    · -- i ≠ j: T j i = 0, so star (T j i) = 0.
      rw [Matrix.one_apply, if_neg hij]
      have h_zero : T j i = 0 := h_diag j i (Ne.symm hij)
      rw [h_zero]; simp
  · -- For k ≠ i in univ: T i k = 0, so the term is 0.
    intros k _ hki
    rw [h_diag i k (Ne.symm hki)]; ring
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-! ## Unitary conjugation preserves powers, trace, and Frobenius² -/

/-- For unitary `U` (`U * Uᴴ = 1`), `(Uᴴ M U)² = Uᴴ (M²) U`. -/
theorem unitary_conj_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U M : Matrix ι ι ℂ} (hU : U * Uᴴ = 1) :
    Uᴴ * M * U * (Uᴴ * M * U) = Uᴴ * (M * M) * U := by
  rw [show Uᴴ * M * U * (Uᴴ * M * U) = Uᴴ * M * (U * Uᴴ) * M * U from by
        simp only [Matrix.mul_assoc]]
  rw [hU, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

/-- For unitary `U` (`U * Uᴴ = 1`), `(Uᴴ M U)³ = Uᴴ (M³) U`. -/
theorem unitary_conj_cb {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U M : Matrix ι ι ℂ} (hU : U * Uᴴ = 1) :
    (Uᴴ * M * U) * (Uᴴ * M * U) * (Uᴴ * M * U) = Uᴴ * (M * M * M) * U := by
  rw [unitary_conj_sq hU]
  rw [show Uᴴ * (M * M) * U * (Uᴴ * M * U) = Uᴴ * (M * M) * (U * Uᴴ) * M * U from by
        simp only [Matrix.mul_assoc]]
  rw [hU, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

/-- For unitary `U`, `Tr((Uᴴ M U)³) = Tr(M³)`. -/
theorem trace_unitary_conj_cb {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U M : Matrix ι ι ℂ} (hUU' : U * Uᴴ = 1) :
    ((Uᴴ * M * U) * (Uᴴ * M * U) * (Uᴴ * M * U)).trace = (M * M * M).trace := by
  rw [unitary_conj_cb hUU']
  rw [Matrix.trace_mul_cycle Uᴴ (M * M * M) U]
  rw [show U * Uᴴ * (M * M * M) = M * M * M from by rw [hUU', Matrix.one_mul]]

/-- For unitary `U`, `‖(Uᴴ M U)²‖²_F = ‖M²‖²_F`. -/
theorem frobNormSq_F_unitary_conj_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U M : Matrix ι ι ℂ} (hUU : Uᴴ * U = 1) (hUU' : U * Uᴴ = 1) :
    frobNormSq_F (Uᴴ * M * U * (Uᴴ * M * U)) = frobNormSq_F (M * M) := by
  rw [unitary_conj_sq hUU']
  rw [frobNormSq_F_unitary_mul_right (Uᴴ * (M * M)) U hUU']
  have hUH : (Uᴴ)ᴴ * Uᴴ = 1 := by
    rw [Matrix.conjTranspose_conjTranspose]; exact hUU'
  rw [frobNormSq_F_unitary_mul_left Uᴴ (M * M) hUH]

/-! ## Schur's inequality -/

/-- **Schur's inequality (diagonal form).**
    There exists a unitary `U` such that the diagonal of `Uᴴ · A · U`,
    a multiset of eigenvalues of `A`, has its sum-of-squared-moduli
    bounded by the Frobenius² norm of `A`. -/
theorem schur_inequality_diag_form (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ,
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      IsUpperTriangular (Uᴴ * A * U) ∧
      (∑ i : Fin n, Complex.normSq ((Uᴴ * A * U) i i)) ≤ frobNormSq_F A := by
  obtain ⟨U, hUU, hUU', hUTri⟩ := matrix_unitary_schur_form A
  refine ⟨U, hUU, hUU', hUTri, ?_⟩
  -- Use unitary invariance to reduce to the diagonal-vs-Frobenius bound.
  have h1 : frobNormSq_F (Uᴴ * A * U) = frobNormSq_F A := by
    rw [frobNormSq_F_unitary_mul_right (Uᴴ * A) U hUU']
    have hUH : (Uᴴ)ᴴ * Uᴴ = 1 := by
      rw [Matrix.conjTranspose_conjTranspose]; exact hUU'
    rw [frobNormSq_F_unitary_mul_left Uᴴ A hUH]
  rw [← h1]
  exact frobNormSq_F_ge_sum_diag (Uᴴ * A * U)

end
