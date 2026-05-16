/-
  HyperCubeGroup.ActiveSubspaceConstruction

  Construction of the unitary candidate `Θ'` from a feasible nondegenerate
  parameter `Θ`. Uses the generic active-subspace machinery
  (`ActiveSubspaceGeneric`) applied to:
    * `Θ.A a` (for the A side)
    * `Θ.B b` (for the B side)
    * `(Θ.C c)ᴴ` (for the C side, since the C-shared Gram is `Cᴴ · C`)

  Provides:
    * `frobNormSq_re_pos_of_ne_zero`: from frobNormSq M ≠ 0 to (frobNormSq M).re > 0.
    * `frobNormSq_conjTranspose`: ‖Mᴴ‖² = ‖M‖².
    * `liftedUnitaryC`: the conjTranspose of the lifted unitary applied to Cᴴ.
    * `activeSubspaceConstruction`: the constructed Θ' and its unitarity.
-/

import HyperCubeGroup.ActiveSubspaceGeneric
import HyperCubeGroup.GroupIsotope

open Matrix BigOperators Complex
open scoped ComplexOrder

noncomputable section

namespace ActiveSubspaceConstruction

variable {n : ℕ} [NeZero n]

open ActiveSubspaceGeneric

/-- For real-valued `frobNormSq M`, nonzero means positive real part. -/
theorem frobNormSq_re_pos_of_ne_zero (M : Matrix (Fin n) (Fin n) ℂ)
    (h : frobNormSq M ≠ 0) :
    0 < (frobNormSq M).re := by
  have hnn : 0 ≤ (frobNormSq M).re := frobNormSq_nonneg M
  have him : (frobNormSq M).im = 0 := frobNormSq_real M
  have hre_ne : (frobNormSq M).re ≠ 0 := by
    intro h_re
    apply h
    apply Complex.ext
    · exact h_re
    · exact him
  exact lt_of_le_of_ne hnn (Ne.symm hre_ne)

/-- `frobNormSq Mᴴ = frobNormSq M` (both equal `Tr(Mᴴ M) = Tr(M Mᴴ)` by trace cyclicity). -/
theorem frobNormSq_conjTranspose_eq (M : Matrix (Fin n) (Fin n) ℂ) :
    frobNormSq Mᴴ = frobNormSq M := by
  unfold frobNormSq frobInner
  rw [Matrix.conjTranspose_conjTranspose, Matrix.trace_mul_comm]

/-! ## C-side lifted unitary `(liftedUnitary Cᴴ)ᴴ` -/

/-- The C-side lifted unitary: applies the active-subspace machinery
    to `Cᴴ`, then takes the conjTranspose to get the unitary candidate
    for the C side. Equivalently, `Q_C · U_Xᴴ` where `Q_C` is the active
    unitary built from `gramOf Cᴴ = (1/γ) Cᴴ C`. -/
noncomputable def liftedUnitaryC (C : Matrix (Fin n) (Fin n) ℂ)
    (hα_pos : 0 < (frobNormSq C).re) : Matrix (Fin n) (Fin n) ℂ :=
  (liftedUnitary Cᴴ
    (by rw [frobNormSq_conjTranspose_eq]; exact hα_pos)).conjTranspose

theorem liftedUnitaryC_mul_conjTranspose (C : Matrix (Fin n) (Fin n) ℂ)
    (hα_pos : 0 < (frobNormSq C).re) :
    liftedUnitaryC C hα_pos * (liftedUnitaryC C hα_pos).conjTranspose = 1 := by
  unfold liftedUnitaryC
  rw [Matrix.conjTranspose_conjTranspose]
  exact liftedUnitary_conjTranspose_mul Cᴴ _

theorem liftedUnitaryC_conjTranspose_mul (C : Matrix (Fin n) (Fin n) ℂ)
    (hα_pos : 0 < (frobNormSq C).re) :
    (liftedUnitaryC C hα_pos).conjTranspose * liftedUnitaryC C hα_pos = 1 := by
  unfold liftedUnitaryC
  rw [Matrix.conjTranspose_conjTranspose]
  exact liftedUnitary_mul_conjTranspose Cᴴ _

/-! ## Construction of Θ' -/

/-- The constructed unitary candidate Θ' from a feasible nondegenerate Θ.
    Each slice is replaced by the corresponding lifted unitary. -/
noncomputable def activeSubspaceTheta' (Θ : HCParams n) (hnd : Nondegenerate Θ) :
    HCParams n where
  A a := liftedUnitary (Θ.A a) (frobNormSq_re_pos_of_ne_zero (Θ.A a) (hnd.A_pos a))
  B b := liftedUnitary (Θ.B b) (frobNormSq_re_pos_of_ne_zero (Θ.B b) (hnd.B_pos b))
  C c := liftedUnitaryC (Θ.C c) (frobNormSq_re_pos_of_ne_zero (Θ.C c) (hnd.C_pos c))

/-- Unitarity of the A-slice in Θ'. -/
theorem activeSubspaceTheta'_A_unitary (Θ : HCParams n) (hnd : Nondegenerate Θ)
    (a : Fin n) :
    (activeSubspaceTheta' Θ hnd).A a *
      ((activeSubspaceTheta' Θ hnd).A a).conjTranspose = 1 :=
  liftedUnitary_mul_conjTranspose _ _

/-- Unitarity of the B-slice in Θ'. -/
theorem activeSubspaceTheta'_B_unitary (Θ : HCParams n) (hnd : Nondegenerate Θ)
    (b : Fin n) :
    (activeSubspaceTheta' Θ hnd).B b *
      ((activeSubspaceTheta' Θ hnd).B b).conjTranspose = 1 :=
  liftedUnitary_mul_conjTranspose _ _

/-- Unitarity of the C-slice in Θ'. -/
theorem activeSubspaceTheta'_C_unitary (Θ : HCParams n) (hnd : Nondegenerate Θ)
    (c : Fin n) :
    (activeSubspaceTheta' Θ hnd).C c *
      ((activeSubspaceTheta' Θ hnd).C c).conjTranspose = 1 :=
  liftedUnitaryC_mul_conjTranspose (Θ.C c)
    (frobNormSq_re_pos_of_ne_zero (Θ.C c) (hnd.C_pos c))

/-! ## Each slice has unit Frobenius norm² (since unitary) -/

theorem frobNormSq_activeSubspaceTheta'_A (Θ : HCParams n) (hnd : Nondegenerate Θ)
    (a : Fin n) :
    frobNormSq ((activeSubspaceTheta' Θ hnd).A a) = 1 :=
  frobNormSq_unitary_eq_one _ (activeSubspaceTheta'_A_unitary Θ hnd a)

theorem frobNormSq_activeSubspaceTheta'_B (Θ : HCParams n) (hnd : Nondegenerate Θ)
    (b : Fin n) :
    frobNormSq ((activeSubspaceTheta' Θ hnd).B b) = 1 :=
  frobNormSq_unitary_eq_one _ (activeSubspaceTheta'_B_unitary Θ hnd b)

theorem frobNormSq_activeSubspaceTheta'_C (Θ : HCParams n) (hnd : Nondegenerate Θ)
    (c : Fin n) :
    frobNormSq ((activeSubspaceTheta' Θ hnd).C c) = 1 :=
  frobNormSq_unitary_eq_one _ (activeSubspaceTheta'_C_unitary Θ hnd c)

/-! ## Nondegeneracy of Θ' -/

theorem activeSubspaceTheta'_Nondegenerate (Θ : HCParams n) (hnd : Nondegenerate Θ) :
    Nondegenerate (activeSubspaceTheta' Θ hnd) where
  A_pos a := by rw [frobNormSq_activeSubspaceTheta'_A]; exact one_ne_zero
  B_pos b := by rw [frobNormSq_activeSubspaceTheta'_B]; exact one_ne_zero
  C_pos c := by rw [frobNormSq_activeSubspaceTheta'_C]; exact one_ne_zero

/-! ## Bridge: shared Gram matrix under PerfectCollinearity -/

/-- `gramOf (Θ.A a) = gramA Θ a`. -/
theorem gramOf_A_eq_gramA (Θ : HCParams n) (a : Fin n) :
    gramOf (Θ.A a) = gramA Θ a := rfl

/-- `gramOf Cᴴ = (1/γ) · Cᴴ · C` (the C-side shared Gram structure). -/
theorem gramOf_conjTranspose_C_eq (Θ : HCParams n) (c : Fin n) :
    gramOf (Θ.C c)ᴴ =
    (1 / frobNormSq (Θ.C c)) • ((Θ.C c).conjTranspose * Θ.C c) := by
  unfold gramOf
  rw [Matrix.conjTranspose_conjTranspose, frobNormSq_conjTranspose_eq]

/-- **Bridge to `shared_gram_matrices`:** under PerfectCollinearity +
    Nondegenerate + Factorizes, the generic gram matrices `gramOf (Θ.A a)`
    and `gramOf (Θ.C c)ᴴ` all coincide with the shared Gram `X`. -/
theorem shared_gram_via_gramOf (Θ : HCParams n) (f : BinOp n)
    (hq : IsQuasigroup f) (hnd : Nondegenerate Θ)
    (hcol : PerfectCollinearity Θ f) (hfeas : Factorizes Θ f) :
    ∃ X : Matrix (Fin n) (Fin n) ℂ,
      (∀ a : Fin n, gramOf (Θ.A a) = X) ∧
      (∀ c : Fin n, gramOf (Θ.C c)ᴴ = X) := by
  obtain ⟨X, hgA, hgC⟩ := shared_gram_matrices Θ f hq hnd hcol hfeas
  refine ⟨X, ?_, ?_⟩
  · intro a; rw [gramOf_A_eq_gramA]; exact hgA a
  · intro c; rw [gramOf_conjTranspose_C_eq]; exact hgC c

/-! ## κ=1 case: discharge via rescaleByNorm

In the κ=1 case (where the shared Gram matrix `X` equals the identity,
i.e. `gramA Θ a = 1` for all `a` by `kappa_one_iff_unitary`), the
active-subspace construction reduces to the simple rescaling
`A → A/√α`. We show that this rescaling preserves `Factorizes` and
`PerfectCollinearity`.

This gives a discharge of `collinear_to_unitary_collinear` in the
κ=1 case as a separate theorem (without requiring the active-subspace
machinery for the κ<1 case). -/

/-- Helper: `(1/√α)² = 1/α` for nonneg real α. -/
private theorem sqrt_inv_sq (α : ℝ) (hα : 0 ≤ α) :
    (Real.sqrt α)⁻¹ * (Real.sqrt α)⁻¹ = α⁻¹ := by
  rw [← mul_inv]; congr 1
  rw [← sq, Real.sq_sqrt hα]

/-- Helper: `((1/√α)⁻¹ : ℂ) * ((1/√α)⁻¹ : ℂ) = (α : ℂ)⁻¹`. -/
private theorem sqrt_inv_sq_C (α : ℝ) (hα : 0 ≤ α) :
    ((Real.sqrt α)⁻¹ : ℂ) * ((Real.sqrt α)⁻¹ : ℂ) = (α : ℂ)⁻¹ := by
  have h := sqrt_inv_sq α hα
  exact_mod_cast h

/-- Rescaling by 1/√α gives unit Frobenius norm². -/
theorem frobNormSq_rescaleByNorm_A (Θ : HCParams n) (a : Fin n)
    (hα : frobNormSq (Θ.A a) ≠ 0) :
    frobNormSq ((rescaleByNorm Θ).A a) = 1 := by
  show frobNormSq (((Real.sqrt (frobNormSq (Θ.A a)).re)⁻¹ : ℂ) • Θ.A a) = 1
  rw [frobNormSq_smul]
  have hα_pos : 0 < (frobNormSq (Θ.A a)).re :=
    frobNormSq_re_pos_of_ne_zero (Θ.A a) hα
  have hstar : starRingEnd ℂ ((Real.sqrt (frobNormSq (Θ.A a)).re)⁻¹ : ℂ) =
      ((Real.sqrt (frobNormSq (Θ.A a)).re)⁻¹ : ℂ) := by
    rw [show ((Real.sqrt (frobNormSq (Θ.A a)).re)⁻¹ : ℂ) =
          (((Real.sqrt (frobNormSq (Θ.A a)).re)⁻¹ : ℝ) : ℂ) from by push_cast; rfl]
    simp
  rw [hstar]
  rw [sqrt_inv_sq_C _ (le_of_lt hα_pos)]
  rw [show frobNormSq (Θ.A a) = ((frobNormSq (Θ.A a)).re : ℂ) from
    frobNormSq_eq_re_complex (Θ.A a)]
  have hα_C : ((frobNormSq (Θ.A a)).re : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact ne_of_gt hα_pos
  simp
  field_simp

theorem frobNormSq_rescaleByNorm_B (Θ : HCParams n) (b : Fin n)
    (hβ : frobNormSq (Θ.B b) ≠ 0) :
    frobNormSq ((rescaleByNorm Θ).B b) = 1 := by
  show frobNormSq (((Real.sqrt (frobNormSq (Θ.B b)).re)⁻¹ : ℂ) • Θ.B b) = 1
  rw [frobNormSq_smul]
  have hβ_pos : 0 < (frobNormSq (Θ.B b)).re :=
    frobNormSq_re_pos_of_ne_zero (Θ.B b) hβ
  have hstar : starRingEnd ℂ ((Real.sqrt (frobNormSq (Θ.B b)).re)⁻¹ : ℂ) =
      ((Real.sqrt (frobNormSq (Θ.B b)).re)⁻¹ : ℂ) := by
    rw [show ((Real.sqrt (frobNormSq (Θ.B b)).re)⁻¹ : ℂ) =
          (((Real.sqrt (frobNormSq (Θ.B b)).re)⁻¹ : ℝ) : ℂ) from by push_cast; rfl]
    simp
  rw [hstar]
  rw [sqrt_inv_sq_C _ (le_of_lt hβ_pos)]
  rw [show frobNormSq (Θ.B b) = ((frobNormSq (Θ.B b)).re : ℂ) from
    frobNormSq_eq_re_complex (Θ.B b)]
  have hβ_C : ((frobNormSq (Θ.B b)).re : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact ne_of_gt hβ_pos
  simp
  field_simp

theorem frobNormSq_rescaleByNorm_C (Θ : HCParams n) (c : Fin n)
    (hγ : frobNormSq (Θ.C c) ≠ 0) :
    frobNormSq ((rescaleByNorm Θ).C c) = 1 := by
  show frobNormSq (((Real.sqrt (frobNormSq (Θ.C c)).re)⁻¹ : ℂ) • Θ.C c) = 1
  rw [frobNormSq_smul]
  have hγ_pos : 0 < (frobNormSq (Θ.C c)).re :=
    frobNormSq_re_pos_of_ne_zero (Θ.C c) hγ
  have hstar : starRingEnd ℂ ((Real.sqrt (frobNormSq (Θ.C c)).re)⁻¹ : ℂ) =
      ((Real.sqrt (frobNormSq (Θ.C c)).re)⁻¹ : ℂ) := by
    rw [show ((Real.sqrt (frobNormSq (Θ.C c)).re)⁻¹ : ℂ) =
          (((Real.sqrt (frobNormSq (Θ.C c)).re)⁻¹ : ℝ) : ℂ) from by push_cast; rfl]
    simp
  rw [hstar]
  rw [sqrt_inv_sq_C _ (le_of_lt hγ_pos)]
  rw [show frobNormSq (Θ.C c) = ((frobNormSq (Θ.C c)).re : ℂ) from
    frobNormSq_eq_re_complex (Θ.C c)]
  have hγ_C : ((frobNormSq (Θ.C c)).re : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact ne_of_gt hγ_pos
  simp
  field_simp

theorem rescaleByNorm_Nondegenerate (Θ : HCParams n) (hnd : Nondegenerate Θ) :
    Nondegenerate (rescaleByNorm Θ) where
  A_pos a := by rw [frobNormSq_rescaleByNorm_A Θ a (hnd.A_pos a)]; exact one_ne_zero
  B_pos b := by rw [frobNormSq_rescaleByNorm_B Θ b (hnd.B_pos b)]; exact one_ne_zero
  C_pos c := by rw [frobNormSq_rescaleByNorm_C Θ c (hnd.C_pos c)]; exact one_ne_zero

/-! ## Trace formula for rescaleByNorm -/

/-- The trace of the rescaled triple's product is `(1/(√α·√β·√γ))` times
    the trace of the original triple's product. -/
theorem trace_product_rescaleByNorm (Θ : HCParams n) (a b c : Fin n) :
    Matrix.trace ((rescaleByNorm Θ).A a * (rescaleByNorm Θ).B b *
      (rescaleByNorm Θ).C c) =
    (((Real.sqrt (frobNormSq (Θ.A a)).re)⁻¹ : ℂ) *
      ((Real.sqrt (frobNormSq (Θ.B b)).re)⁻¹ : ℂ) *
      ((Real.sqrt (frobNormSq (Θ.C c)).re)⁻¹ : ℂ)) *
    Matrix.trace (Θ.A a * Θ.B b * Θ.C c) := by
  show Matrix.trace
    (((Real.sqrt (frobNormSq (Θ.A a)).re)⁻¹ : ℂ) • Θ.A a *
      (((Real.sqrt (frobNormSq (Θ.B b)).re)⁻¹ : ℂ) • Θ.B b) *
      (((Real.sqrt (frobNormSq (Θ.C c)).re)⁻¹ : ℂ) • Θ.C c)) = _
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul]
  simp only [Matrix.trace_smul, smul_eq_mul]
  ring

/-- `hcProduct (rescaleByNorm Θ) a b c = scaleProduct · hcProduct Θ a b c`
    where `scaleProduct = 1/(√α · √β · √γ)`. -/
theorem hcProduct_rescaleByNorm (Θ : HCParams n) (a b c : Fin n) :
    hcProduct (rescaleByNorm Θ) a b c =
    (((Real.sqrt (frobNormSq (Θ.A a)).re)⁻¹ : ℂ) *
      ((Real.sqrt (frobNormSq (Θ.B b)).re)⁻¹ : ℂ) *
      ((Real.sqrt (frobNormSq (Θ.C c)).re)⁻¹ : ℂ)) *
    hcProduct Θ a b c := by
  unfold hcProduct
  rw [trace_product_rescaleByNorm]
  ring

/-! ## αβγ = 1 on support, under κ=1 -/

/-- If `kappaTriple Θ a b (f.op a b) = 1` and `Factorizes Θ f`, then
    `αβγ = 1` on the support triple. -/
theorem frobNormSq_prod_eq_one_of_kappa_one (Θ : HCParams n) (f : BinOp n)
    (hfeas : Factorizes Θ f) (a b : Fin n)
    (hκ : kappaTriple Θ a b (f.op a b) = 1) :
    frobNormSq (Θ.A a) * frobNormSq (Θ.B b) * frobNormSq (Θ.C (f.op a b)) = 1 := by
  -- T = hcProduct Θ a b (f.op a b) = 1.
  have hT : hcProduct Θ a b (f.op a b) = 1 := by
    have := hfeas a b (f.op a b)
    rwa [structureTensor, if_pos rfl] at this
  -- kappaTriple = αβγ / (T · star T). With T = 1: kappaTriple = αβγ.
  unfold kappaTriple at hκ
  rw [hT] at hκ
  simp at hκ
  exact hκ

/-- The product `√α · √β · √γ` equals 1 on support under κ=1. -/
theorem sqrt_prod_eq_one_of_kappa_one (Θ : HCParams n) (f : BinOp n)
    (hfeas : Factorizes Θ f) (hnd : Nondegenerate Θ) (a b : Fin n)
    (hκ : kappaTriple Θ a b (f.op a b) = 1) :
    Real.sqrt (frobNormSq (Θ.A a)).re *
    Real.sqrt (frobNormSq (Θ.B b)).re *
    Real.sqrt (frobNormSq (Θ.C (f.op a b))).re = 1 := by
  -- αβγ = 1 (from kappa=1).
  have h_prod := frobNormSq_prod_eq_one_of_kappa_one Θ f hfeas a b hκ
  have hα_pos := frobNormSq_re_pos_of_ne_zero (Θ.A a) (hnd.A_pos a)
  have hβ_pos := frobNormSq_re_pos_of_ne_zero (Θ.B b) (hnd.B_pos b)
  have hγ_pos := frobNormSq_re_pos_of_ne_zero (Θ.C (f.op a b))
    (hnd.C_pos (f.op a b))
  have hα_re : (frobNormSq (Θ.A a)).re ≥ 0 := le_of_lt hα_pos
  have hβ_re : (frobNormSq (Θ.B b)).re ≥ 0 := le_of_lt hβ_pos
  have hγ_re : (frobNormSq (Θ.C (f.op a b))).re ≥ 0 := le_of_lt hγ_pos
  -- αβγ = 1 in ℂ ⟹ αβγ.re = 1.
  have h_prod_re :
      (frobNormSq (Θ.A a)).re * (frobNormSq (Θ.B b)).re *
        (frobNormSq (Θ.C (f.op a b))).re = 1 := by
    have h1 : (frobNormSq (Θ.A a) * frobNormSq (Θ.B b) *
        frobNormSq (Θ.C (f.op a b))).re = 1 := by
      rw [h_prod]; rfl
    rw [Complex.mul_re, Complex.mul_re, frobNormSq_real, frobNormSq_real,
        frobNormSq_real, mul_zero, sub_zero, mul_zero, sub_zero] at h1
    exact h1
  -- (√α · √β · √γ)² = αβγ = 1 ⟹ √α · √β · √γ = 1 (positive).
  have h_sqrt_sq :
      (Real.sqrt (frobNormSq (Θ.A a)).re *
        Real.sqrt (frobNormSq (Θ.B b)).re *
        Real.sqrt (frobNormSq (Θ.C (f.op a b))).re)^2 = 1 := by
    rw [show (Real.sqrt (frobNormSq (Θ.A a)).re *
              Real.sqrt (frobNormSq (Θ.B b)).re *
              Real.sqrt (frobNormSq (Θ.C (f.op a b))).re)^2 =
            (Real.sqrt (frobNormSq (Θ.A a)).re)^2 *
            (Real.sqrt (frobNormSq (Θ.B b)).re)^2 *
            (Real.sqrt (frobNormSq (Θ.C (f.op a b))).re)^2 from by ring]
    rw [Real.sq_sqrt hα_re, Real.sq_sqrt hβ_re, Real.sq_sqrt hγ_re]
    exact h_prod_re
  have h_sqrt_pos :
      0 < Real.sqrt (frobNormSq (Θ.A a)).re *
            Real.sqrt (frobNormSq (Θ.B b)).re *
            Real.sqrt (frobNormSq (Θ.C (f.op a b))).re :=
    mul_pos (mul_pos (Real.sqrt_pos.mpr hα_pos) (Real.sqrt_pos.mpr hβ_pos))
      (Real.sqrt_pos.mpr hγ_pos)
  nlinarith

/-! ## Factorizes (rescaleByNorm Θ) f under κ=1 -/

/-- Under κ=1 + Factorizes Θ f + Nondegenerate Θ, the rescaled triple
    is also factorising. -/
theorem Factorizes_rescaleByNorm_of_kappa_one (Θ : HCParams n) (f : BinOp n)
    (hfeas : Factorizes Θ f) (hnd : Nondegenerate Θ)
    (hκ : ∀ a b : Fin n, kappaTriple Θ a b (f.op a b) = 1) :
    Factorizes (rescaleByNorm Θ) f := by
  intro a b c
  rw [hcProduct_rescaleByNorm]
  by_cases hc : c = f.op a b
  · -- On support: αβγ = 1, T = 1.
    subst hc
    have h_sqrt := sqrt_prod_eq_one_of_kappa_one Θ f hfeas hnd a b (hκ a b)
    have hT : hcProduct Θ a b (f.op a b) = 1 := by
      have := hfeas a b (f.op a b)
      rwa [structureTensor, if_pos rfl] at this
    rw [hT]
    -- (1/√α)(1/√β)(1/√γ) · 1 = 1.
    have hα_pos := frobNormSq_re_pos_of_ne_zero (Θ.A a) (hnd.A_pos a)
    have hβ_pos := frobNormSq_re_pos_of_ne_zero (Θ.B b) (hnd.B_pos b)
    have hγ_pos := frobNormSq_re_pos_of_ne_zero (Θ.C (f.op a b))
      (hnd.C_pos (f.op a b))
    have h_sα := Real.sqrt_pos.mpr hα_pos
    have h_sβ := Real.sqrt_pos.mpr hβ_pos
    have h_sγ := Real.sqrt_pos.mpr hγ_pos
    -- Show the product of inverses, when multiplied by 1, equals 1 = structureTensor.
    rw [structureTensor, if_pos rfl]
    have h_C : ((Real.sqrt (frobNormSq (Θ.A a)).re)⁻¹ : ℂ) *
        ((Real.sqrt (frobNormSq (Θ.B b)).re)⁻¹ : ℂ) *
        ((Real.sqrt (frobNormSq (Θ.C (f.op a b))).re)⁻¹ : ℂ) = 1 := by
      have h_sqrt_C :
          (Real.sqrt (frobNormSq (Θ.A a)).re : ℂ) *
          (Real.sqrt (frobNormSq (Θ.B b)).re : ℂ) *
          (Real.sqrt (frobNormSq (Θ.C (f.op a b))).re : ℂ) = 1 := by
        exact_mod_cast h_sqrt
      rw [show
          ((Real.sqrt (frobNormSq (Θ.A a)).re)⁻¹ : ℂ) *
          ((Real.sqrt (frobNormSq (Θ.B b)).re)⁻¹ : ℂ) *
          ((Real.sqrt (frobNormSq (Θ.C (f.op a b))).re)⁻¹ : ℂ) =
          ((Real.sqrt (frobNormSq (Θ.A a)).re : ℂ) *
            (Real.sqrt (frobNormSq (Θ.B b)).re : ℂ) *
            (Real.sqrt (frobNormSq (Θ.C (f.op a b))).re : ℂ))⁻¹
          from by rw [mul_inv, mul_inv]]
      rw [h_sqrt_C, inv_one]
    rw [h_C, mul_one]
  · -- Off support: hcProduct Θ a b c = 0.
    have h_off : hcProduct Θ a b c = 0 := by
      have := hfeas a b c
      rwa [structureTensor, if_neg (Ne.symm hc)] at this
    rw [h_off, mul_zero]
    rw [structureTensor, if_neg (Ne.symm hc)]

/-! ## PerfectCollinearity (rescaleByNorm Θ) f -/

/-- The conjTranspose of a real-cast smul: `(((r : ℝ) : ℂ) • M)ᴴ = ((r : ℝ) : ℂ) • Mᴴ`. -/
private theorem conjTranspose_real_smul (r : ℝ) (M : Matrix (Fin n) (Fin n) ℂ) :
    ((r : ℂ) • M).conjTranspose = (r : ℂ) • M.conjTranspose := by
  rw [Matrix.conjTranspose_smul]; simp

/-- The conjTranspose of `(↑r)⁻¹ • M` for `r : ℝ`. -/
private theorem conjTranspose_real_inv_smul (r : ℝ) (M : Matrix (Fin n) (Fin n) ℂ) :
    (((r : ℂ))⁻¹ • M).conjTranspose = ((r : ℂ))⁻¹ • M.conjTranspose := by
  rw [Matrix.conjTranspose_smul]
  congr 1
  rw [show ((r : ℂ))⁻¹ = (((r⁻¹ : ℝ)) : ℂ) from by push_cast; rfl]
  simp

/-- **PerfectCollinearity (rescaleByNorm Θ) f.**
    Rescaling preserves perfect collinearity (no κ=1 hypothesis needed). -/
theorem PerfectCollinearity_rescaleByNorm (Θ : HCParams n) (f : BinOp n)
    (hcol : PerfectCollinearity Θ f) (hnd : Nondegenerate Θ) :
    PerfectCollinearity (rescaleByNorm Θ) f := by
  rw [perfectCollinearity_iff_identities _ _ (rescaleByNorm_Nondegenerate Θ hnd)]
  obtain ⟨idA, idB, idC⟩ := (perfectCollinearity_iff_identities Θ f hnd).mp hcol
  refine ⟨?_, ?_, ?_⟩
  · -- idA for rescaled: Θ'.B * Θ'.C = (T'/α') · Θ'.Aᴴ.
    intro a b
    set c := f.op a b
    set sqα := (Real.sqrt (frobNormSq (Θ.A a)).re : ℂ)
    set sqβ := (Real.sqrt (frobNormSq (Θ.B b)).re : ℂ)
    set sqγ := (Real.sqrt (frobNormSq (Θ.C c)).re : ℂ)
    have hα_pos := frobNormSq_re_pos_of_ne_zero (Θ.A a) (hnd.A_pos a)
    have hsqα_pos : 0 < Real.sqrt (frobNormSq (Θ.A a)).re :=
      Real.sqrt_pos.mpr hα_pos
    have h_sqα_C_ne : sqα ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt hsqα_pos)
    show ((sqβ)⁻¹ • Θ.B b) * ((sqγ)⁻¹ • Θ.C c) =
        (hcProduct (rescaleByNorm Θ) a b c /
          frobNormSq ((rescaleByNorm Θ).A a)) •
          ((sqα)⁻¹ • Θ.A a).conjTranspose
    rw [frobNormSq_rescaleByNorm_A Θ a (hnd.A_pos a)]
    rw [hcProduct_rescaleByNorm]
    show ((sqβ)⁻¹ • Θ.B b) * ((sqγ)⁻¹ • Θ.C c) =
        ((sqα)⁻¹ * (sqβ)⁻¹ * (sqγ)⁻¹ * hcProduct Θ a b c / 1) •
          ((sqα)⁻¹ • Θ.A a).conjTranspose
    rw [div_one]
    rw [Matrix.smul_mul, Matrix.mul_smul]
    rw [idA a b]
    show ((sqβ)⁻¹ • ((sqγ)⁻¹ •
            ((hcProduct Θ a b c / frobNormSq (Θ.A a)) •
              (Θ.A a).conjTranspose))) =
        ((sqα)⁻¹ * (sqβ)⁻¹ * (sqγ)⁻¹ * hcProduct Θ a b c) •
          ((sqα)⁻¹ • Θ.A a).conjTranspose
    rw [conjTranspose_real_inv_smul]
    rw [smul_smul, smul_smul, smul_smul]
    -- Both sides are scalar multiples of (Θ.A a)ᴴ. Compare scalars.
    congr 1
    -- Goal: sqβ⁻¹ * (sqγ⁻¹ * (T/α)) = (sqα⁻¹ * sqβ⁻¹ * sqγ⁻¹ * T) * sqα⁻¹.
    -- α = sqα², so 1/α = sqα⁻¹·sqα⁻¹.
    have h_sqα_sq : sqα * sqα = (frobNormSq (Θ.A a) : ℂ) := by
      have := sqrt_inv_sq (frobNormSq (Θ.A a)).re (le_of_lt hα_pos)
      have h_sqα_sq_R : (Real.sqrt (frobNormSq (Θ.A a)).re)^2 =
          (frobNormSq (Θ.A a)).re := Real.sq_sqrt (le_of_lt hα_pos)
      rw [show sqα * sqα = ((Real.sqrt (frobNormSq (Θ.A a)).re)^2 : ℂ) from by
        push_cast; ring]
      rw [show ((Real.sqrt (frobNormSq (Θ.A a)).re)^2 : ℂ) =
          ((frobNormSq (Θ.A a)).re : ℂ) from by exact_mod_cast h_sqα_sq_R]
      rw [← frobNormSq_eq_re_complex]
    have hα_C_ne : (frobNormSq (Θ.A a) : ℂ) ≠ 0 := hnd.A_pos a
    field_simp
    linear_combination (hcProduct Θ a b c * sqβ⁻¹ * sqγ⁻¹) * h_sqα_sq
  · -- idB for rescaled. Same structure.
    intro a b
    set c := f.op a b
    set sqα := (Real.sqrt (frobNormSq (Θ.A a)).re : ℂ)
    set sqβ := (Real.sqrt (frobNormSq (Θ.B b)).re : ℂ)
    set sqγ := (Real.sqrt (frobNormSq (Θ.C c)).re : ℂ)
    have hβ_pos := frobNormSq_re_pos_of_ne_zero (Θ.B b) (hnd.B_pos b)
    have hsqβ_pos : 0 < Real.sqrt (frobNormSq (Θ.B b)).re :=
      Real.sqrt_pos.mpr hβ_pos
    have h_sqβ_C_ne : sqβ ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt hsqβ_pos)
    show ((sqγ)⁻¹ • Θ.C c) * ((sqα)⁻¹ • Θ.A a) =
        (hcProduct (rescaleByNorm Θ) a b c /
          frobNormSq ((rescaleByNorm Θ).B b)) •
          ((sqβ)⁻¹ • Θ.B b).conjTranspose
    rw [frobNormSq_rescaleByNorm_B Θ b (hnd.B_pos b)]
    rw [hcProduct_rescaleByNorm]
    show ((sqγ)⁻¹ • Θ.C c) * ((sqα)⁻¹ • Θ.A a) =
        ((sqα)⁻¹ * (sqβ)⁻¹ * (sqγ)⁻¹ * hcProduct Θ a b c / 1) •
          ((sqβ)⁻¹ • Θ.B b).conjTranspose
    rw [div_one]
    rw [Matrix.smul_mul, Matrix.mul_smul]
    rw [idB a b]
    rw [conjTranspose_real_inv_smul]
    rw [smul_smul, smul_smul, smul_smul]
    congr 1
    have h_sqβ_sq : sqβ * sqβ = (frobNormSq (Θ.B b) : ℂ) := by
      have h_sqβ_sq_R : (Real.sqrt (frobNormSq (Θ.B b)).re)^2 =
          (frobNormSq (Θ.B b)).re := Real.sq_sqrt (le_of_lt hβ_pos)
      rw [show sqβ * sqβ = ((Real.sqrt (frobNormSq (Θ.B b)).re)^2 : ℂ) from by
        push_cast; ring]
      rw [show ((Real.sqrt (frobNormSq (Θ.B b)).re)^2 : ℂ) =
          ((frobNormSq (Θ.B b)).re : ℂ) from by exact_mod_cast h_sqβ_sq_R]
      rw [← frobNormSq_eq_re_complex]
    have hβ_C_ne : (frobNormSq (Θ.B b) : ℂ) ≠ 0 := hnd.B_pos b
    field_simp
    linear_combination (hcProduct Θ a b c * sqα⁻¹ * sqγ⁻¹) * h_sqβ_sq
  · -- idC for rescaled. Same structure.
    intro a b
    set c := f.op a b with hc_def
    set sqα := (Real.sqrt (frobNormSq (Θ.A a)).re : ℂ)
    set sqβ := (Real.sqrt (frobNormSq (Θ.B b)).re : ℂ)
    set sqγ := (Real.sqrt (frobNormSq (Θ.C c)).re : ℂ)
    have hγ_pos := frobNormSq_re_pos_of_ne_zero (Θ.C c) (hnd.C_pos c)
    have hsqγ_pos : 0 < Real.sqrt (frobNormSq (Θ.C c)).re :=
      Real.sqrt_pos.mpr hγ_pos
    have h_sqγ_C_ne : sqγ ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt hsqγ_pos)
    show ((sqα)⁻¹ • Θ.A a) * ((sqβ)⁻¹ • Θ.B b) =
        (hcProduct (rescaleByNorm Θ) a b c /
          frobNormSq ((rescaleByNorm Θ).C c)) •
          ((sqγ)⁻¹ • Θ.C c).conjTranspose
    rw [frobNormSq_rescaleByNorm_C Θ c (hnd.C_pos c)]
    rw [hcProduct_rescaleByNorm]
    show ((sqα)⁻¹ • Θ.A a) * ((sqβ)⁻¹ • Θ.B b) =
        ((sqα)⁻¹ * (sqβ)⁻¹ * (sqγ)⁻¹ * hcProduct Θ a b c / 1) •
          ((sqγ)⁻¹ • Θ.C c).conjTranspose
    rw [div_one]
    rw [Matrix.smul_mul, Matrix.mul_smul]
    rw [idC a b]
    rw [conjTranspose_real_inv_smul]
    rw [smul_smul, smul_smul, smul_smul]
    congr 1
    have h_sqγ_sq : sqγ * sqγ = (frobNormSq (Θ.C c) : ℂ) := by
      have h_sqγ_sq_R : (Real.sqrt (frobNormSq (Θ.C c)).re)^2 =
          (frobNormSq (Θ.C c)).re := Real.sq_sqrt (le_of_lt hγ_pos)
      rw [show sqγ * sqγ = ((Real.sqrt (frobNormSq (Θ.C c)).re)^2 : ℂ) from by
        push_cast; ring]
      rw [show ((Real.sqrt (frobNormSq (Θ.C c)).re)^2 : ℂ) =
          ((frobNormSq (Θ.C c)).re : ℂ) from by exact_mod_cast h_sqγ_sq_R]
      rw [← frobNormSq_eq_re_complex]
    have hγ_C_ne : (frobNormSq (Θ.C c) : ℂ) ≠ 0 := hnd.C_pos c
    -- Goal: sqα⁻¹ * (sqβ⁻¹ * (T / γ)) = sqα⁻¹ * sqβ⁻¹ * sqγ⁻¹ * T * sqγ⁻¹.
    have h_inv_sq : sqγ⁻¹ * sqγ⁻¹ = (frobNormSq (Θ.C c) : ℂ)⁻¹ := by
      rw [← mul_inv, h_sqγ_sq]
    rw [show sqα⁻¹ * sqβ⁻¹ * sqγ⁻¹ * hcProduct Θ a b c * sqγ⁻¹ =
        sqα⁻¹ * sqβ⁻¹ * (sqγ⁻¹ * sqγ⁻¹) * hcProduct Θ a b c from by ring]
    rw [h_inv_sq]
    rw [← hc_def]
    field_simp

/-! ## Unitarity of rescaled A under κ=1 -/

/-- Under κ=1, the rescaled A slice `(Θ.A a)/√α` is unitary. -/
theorem unitary_rescaleByNorm_A_of_kappa_one (Θ : HCParams n) (f : BinOp n)
    (hq : IsQuasigroup f) (hnd : Nondegenerate Θ)
    (hcol : PerfectCollinearity Θ f) (hfeas : Factorizes Θ f)
    (hκ : ∀ a b : Fin n, kappaTriple Θ a b (f.op a b) = 1)
    (a : Fin n) :
    (rescaleByNorm Θ).A a * ((rescaleByNorm Θ).A a).conjTranspose = 1 := by
  -- gramA Θ a = 1 (by kappa_one_iff_unitary).
  have h_gram : gramA Θ a = 1 :=
    kappa_one_iff_unitary Θ f hq hnd hcol hfeas hκ a
  -- A · Aᴴ = α • gramA = α • I.
  have h_A_AH : Θ.A a * (Θ.A a).conjTranspose = frobNormSq (Θ.A a) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [ActiveSubspaceGeneric.M_mul_conjTranspose_eq_smul_gramOf (Θ.A a) (hnd.A_pos a)]
    show frobNormSq (Θ.A a) • gramOf (Θ.A a) = _
    rw [show gramOf (Θ.A a) = gramA Θ a from rfl, h_gram]
  set sqα := (Real.sqrt (frobNormSq (Θ.A a)).re : ℂ)
  have hα_pos := frobNormSq_re_pos_of_ne_zero (Θ.A a) (hnd.A_pos a)
  have h_sqα_pos := Real.sqrt_pos.mpr hα_pos
  have h_sqα_C_ne : sqα ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt h_sqα_pos)
  show (sqα⁻¹ • Θ.A a) * (sqα⁻¹ • Θ.A a).conjTranspose = 1
  rw [conjTranspose_real_inv_smul]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h_A_AH, smul_smul]
  rw [show sqα⁻¹ * sqα⁻¹ * frobNormSq (Θ.A a) = 1 from ?_]
  · exact one_smul ℂ 1
  · rw [show (sqα⁻¹ : ℂ) * (sqα⁻¹ : ℂ) = (frobNormSq (Θ.A a) : ℂ)⁻¹ from ?_]
    · exact inv_mul_cancel₀ (hnd.A_pos a)
    · rw [← mul_inv]
      have h_sqα_sq : sqα * sqα = (frobNormSq (Θ.A a) : ℂ) := by
        have h_sqα_sq_R : (Real.sqrt (frobNormSq (Θ.A a)).re)^2 =
            (frobNormSq (Θ.A a)).re := Real.sq_sqrt (le_of_lt hα_pos)
        rw [show sqα * sqα = ((Real.sqrt (frobNormSq (Θ.A a)).re)^2 : ℂ) from by
          push_cast; ring]
        rw [show ((Real.sqrt (frobNormSq (Θ.A a)).re)^2 : ℂ) =
            ((frobNormSq (Θ.A a)).re : ℂ) from by exact_mod_cast h_sqα_sq_R]
        rw [← frobNormSq_eq_re_complex]
      rw [h_sqα_sq]

/-! ## Unitarity of rescaled C under κ=1 -/

/-- Under κ=1, `(1/γ) · Cᴴ · C = 1` (from shared_gram_matrices). -/
theorem invFrobNormSq_C_conjTranspose_C_eq_one (Θ : HCParams n) (f : BinOp n)
    (hq : IsQuasigroup f) (hnd : Nondegenerate Θ)
    (hcol : PerfectCollinearity Θ f) (hfeas : Factorizes Θ f)
    (hκ : ∀ a b : Fin n, kappaTriple Θ a b (f.op a b) = 1)
    (c : Fin n) :
    (1 / frobNormSq (Θ.C c)) • ((Θ.C c).conjTranspose * Θ.C c) = 1 := by
  -- From shared_gram_matrices: ∀ c, (1/γ) Cᴴ C = X. From kappa_one_iff_unitary:
  -- gramA Θ a = 1. By shared_gram_matrices, gramA Θ a = X. So X = 1.
  obtain ⟨X, hgA, hgC⟩ := shared_gram_matrices Θ f hq hnd hcol hfeas
  have hgA1 : gramA Θ ⟨0, NeZero.pos n⟩ = 1 :=
    kappa_one_iff_unitary Θ f hq hnd hcol hfeas hκ _
  have hX1 : X = 1 := by rw [← hgA ⟨0, NeZero.pos n⟩]; exact hgA1
  rw [hgC c, hX1]

/-- Under κ=1, `gramOf (Θ.C c) = 1` (i.e., `(1/γ) · C · Cᴴ = 1`). -/
theorem gramOf_C_eq_one_of_kappa_one (Θ : HCParams n) (f : BinOp n)
    (hq : IsQuasigroup f) (hnd : Nondegenerate Θ)
    (hcol : PerfectCollinearity Θ f) (hfeas : Factorizes Θ f)
    (hκ : ∀ a b : Fin n, kappaTriple Θ a b (f.op a b) = 1)
    (c : Fin n) :
    gramOf (Θ.C c) = 1 := by
  -- (1/γ) Cᴴ C = 1 ⟹ ((1/γ) Cᴴ) · C = 1 ⟹ C · ((1/γ) Cᴴ) = 1 ⟹ (1/γ) C Cᴴ = 1.
  have h_left : ((1 / frobNormSq (Θ.C c)) • (Θ.C c).conjTranspose) * Θ.C c = 1 := by
    rw [Matrix.smul_mul]
    exact invFrobNormSq_C_conjTranspose_C_eq_one Θ f hq hnd hcol hfeas hκ c
  have h_right : Θ.C c * ((1 / frobNormSq (Θ.C c)) • (Θ.C c).conjTranspose) = 1 :=
    mul_eq_one_comm.mp h_left
  show (1 / frobNormSq (Θ.C c)) • (Θ.C c * (Θ.C c).conjTranspose) = 1
  rw [← Matrix.mul_smul]
  exact h_right

/-- Under κ=1, the rescaled C slice is unitary. -/
theorem unitary_rescaleByNorm_C_of_kappa_one (Θ : HCParams n) (f : BinOp n)
    (hq : IsQuasigroup f) (hnd : Nondegenerate Θ)
    (hcol : PerfectCollinearity Θ f) (hfeas : Factorizes Θ f)
    (hκ : ∀ a b : Fin n, kappaTriple Θ a b (f.op a b) = 1)
    (c : Fin n) :
    (rescaleByNorm Θ).C c * ((rescaleByNorm Θ).C c).conjTranspose = 1 := by
  have h_gram : gramOf (Θ.C c) = 1 :=
    gramOf_C_eq_one_of_kappa_one Θ f hq hnd hcol hfeas hκ c
  have h_C_CH : Θ.C c * (Θ.C c).conjTranspose =
      frobNormSq (Θ.C c) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [ActiveSubspaceGeneric.M_mul_conjTranspose_eq_smul_gramOf (Θ.C c) (hnd.C_pos c)]
    rw [h_gram]
  set sqγ := (Real.sqrt (frobNormSq (Θ.C c)).re : ℂ)
  have hγ_pos := frobNormSq_re_pos_of_ne_zero (Θ.C c) (hnd.C_pos c)
  have h_sqγ_pos := Real.sqrt_pos.mpr hγ_pos
  have h_sqγ_C_ne : sqγ ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt h_sqγ_pos)
  show (sqγ⁻¹ • Θ.C c) * (sqγ⁻¹ • Θ.C c).conjTranspose = 1
  rw [conjTranspose_real_inv_smul]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h_C_CH, smul_smul]
  rw [show sqγ⁻¹ * sqγ⁻¹ * frobNormSq (Θ.C c) = 1 from ?_]
  · exact one_smul ℂ 1
  · rw [show (sqγ⁻¹ : ℂ) * (sqγ⁻¹ : ℂ) = (frobNormSq (Θ.C c) : ℂ)⁻¹ from ?_]
    · exact inv_mul_cancel₀ (hnd.C_pos c)
    · rw [← mul_inv]
      have h_sqγ_sq : sqγ * sqγ = (frobNormSq (Θ.C c) : ℂ) := by
        have h_sqγ_sq_R : (Real.sqrt (frobNormSq (Θ.C c)).re)^2 =
            (frobNormSq (Θ.C c)).re := Real.sq_sqrt (le_of_lt hγ_pos)
        rw [show sqγ * sqγ = ((Real.sqrt (frobNormSq (Θ.C c)).re)^2 : ℂ) from by
          push_cast; ring]
        rw [show ((Real.sqrt (frobNormSq (Θ.C c)).re)^2 : ℂ) =
            ((frobNormSq (Θ.C c)).re : ℂ) from by exact_mod_cast h_sqγ_sq_R]
        rw [← frobNormSq_eq_re_complex]
      rw [h_sqγ_sq]

/-! ## Unitarity of rescaled B under κ=1

Using the chained collinear identities:
  Bᴴ = β · C · A  (from idB rearranged)
  A · B = (1/γ) Cᴴ  (from idC)
So: Bᴴ · B = β · C · A · B = β · C · (1/γ) Cᴴ = (β/γ) · C · Cᴴ = (β/γ) · γ · I = β · I
(using gramOf_C_eq_one_of_kappa_one for the last step). -/

/-- `Bᴴ · B = β · 1` under κ=1. -/
theorem conjTranspose_B_mul_B_of_kappa_one (Θ : HCParams n) (f : BinOp n)
    (hq : IsQuasigroup f) (hnd : Nondegenerate Θ)
    (hcol : PerfectCollinearity Θ f) (hfeas : Factorizes Θ f)
    (hκ : ∀ a b : Fin n, kappaTriple Θ a b (f.op a b) = 1)
    (a b : Fin n) :
    (Θ.B b).conjTranspose * Θ.B b = frobNormSq (Θ.B b) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  set c := f.op a b with hc_def
  obtain ⟨idA, idB, idC⟩ := (perfectCollinearity_iff_identities Θ f hnd).mp hcol
  have hT : hcProduct Θ a b c = 1 := by
    have := hfeas a b c
    rwa [structureTensor, if_pos rfl] at this
  -- idB: C · A = (T/β) · Bᴴ. With T=1: C · A = (1/β) · Bᴴ. So Bᴴ = β · (C · A).
  have h_BH : (Θ.B b).conjTranspose = frobNormSq (Θ.B b) • (Θ.C c * Θ.A a) := by
    have := idB a b
    show (Θ.B b).conjTranspose = _
    have h_eq : Θ.C c * Θ.A a =
        (1 / frobNormSq (Θ.B b)) • (Θ.B b).conjTranspose := by
      rw [show (1 / frobNormSq (Θ.B b)) = hcProduct Θ a b c / frobNormSq (Θ.B b) from
        by rw [hT]]
      exact this
    rw [h_eq, smul_smul]
    rw [show frobNormSq (Θ.B b) * (1 / frobNormSq (Θ.B b)) = 1 from by
      field_simp; exact div_self (hnd.B_pos b)]
    rw [one_smul]
  -- idC: A · B = (T/γ) · Cᴴ. With T=1: A · B = (1/γ) · Cᴴ.
  have h_AB : Θ.A a * Θ.B b = (1 / frobNormSq (Θ.C c)) • (Θ.C c).conjTranspose := by
    have hidC := idC a b
    dsimp only at hidC
    rw [hT, one_div] at hidC
    rw [hidC]
    rw [show ((1 : ℂ) / frobNormSq (Θ.C c)) = (frobNormSq (Θ.C c))⁻¹ from one_div _]
  -- Bᴴ · B = β · (C · A · B) = β · (C · ((1/γ) · Cᴴ)) = (β/γ) · (C · Cᴴ).
  rw [h_BH]
  rw [Matrix.smul_mul, Matrix.mul_assoc, h_AB]
  rw [Matrix.mul_smul]
  -- = β • ((1/γ) • (C * Cᴴ))
  rw [smul_smul]
  -- = (β · (1/γ)) • (C · Cᴴ)
  -- We have (1/γ) C Cᴴ = 1 from gramOf_C_eq_one_of_kappa_one.
  have h_gramC : (1 / frobNormSq (Θ.C c)) • (Θ.C c * (Θ.C c).conjTranspose) = 1 := by
    have := gramOf_C_eq_one_of_kappa_one Θ f hq hnd hcol hfeas hκ c
    show (1 / frobNormSq (Θ.C c)) • (Θ.C c * (Θ.C c).conjTranspose) = 1
    exact this
  -- β · (1/γ) • (C · Cᴴ) = β • ((1/γ) • (C · Cᴴ)) = β • 1.
  rw [show frobNormSq (Θ.B b) * (1 / frobNormSq (Θ.C c)) =
      frobNormSq (Θ.B b) * (1 / frobNormSq (Θ.C c)) from rfl]
  rw [show (frobNormSq (Θ.B b) * (1 / frobNormSq (Θ.C c))) • (Θ.C c * (Θ.C c).conjTranspose) =
      frobNormSq (Θ.B b) • ((1 / frobNormSq (Θ.C c)) • (Θ.C c * (Θ.C c).conjTranspose))
      from by rw [smul_smul]]
  rw [h_gramC]

/-- Under κ=1, the rescaled B slice is unitary. -/
theorem unitary_rescaleByNorm_B_of_kappa_one (Θ : HCParams n) (f : BinOp n)
    (hq : IsQuasigroup f) (hnd : Nondegenerate Θ)
    (hcol : PerfectCollinearity Θ f) (hfeas : Factorizes Θ f)
    (hκ : ∀ a b : Fin n, kappaTriple Θ a b (f.op a b) = 1)
    (b : Fin n) :
    (rescaleByNorm Θ).B b * ((rescaleByNorm Θ).B b).conjTranspose = 1 := by
  -- Pick any a (use 0).
  have ⟨a₀⟩ : Nonempty (Fin n) := ⟨⟨0, NeZero.pos n⟩⟩
  -- Bᴴ B = β • 1, so by mul_eq_one_comm, B Bᴴ = β • 1.
  have h_BHB : (Θ.B b).conjTranspose * Θ.B b =
      frobNormSq (Θ.B b) • (1 : Matrix (Fin n) (Fin n) ℂ) :=
    conjTranspose_B_mul_B_of_kappa_one Θ f hq hnd hcol hfeas hκ a₀ b
  -- (1/β • Bᴴ) · B = 1.
  have hβ_ne : frobNormSq (Θ.B b) ≠ 0 := hnd.B_pos b
  have h_β_inv_β : (1 / frobNormSq (Θ.B b)) * frobNormSq (Θ.B b) = 1 := by
    rw [one_div]; exact inv_mul_cancel₀ hβ_ne
  have h_β_β_inv : frobNormSq (Θ.B b) * (1 / frobNormSq (Θ.B b)) = 1 := by
    rw [one_div]; exact mul_inv_cancel₀ hβ_ne
  have h_left : ((1 / frobNormSq (Θ.B b)) • (Θ.B b).conjTranspose) * Θ.B b = 1 := by
    rw [Matrix.smul_mul, h_BHB, smul_smul]
    rw [h_β_inv_β]
    rw [one_smul]
  have h_right : Θ.B b * ((1 / frobNormSq (Θ.B b)) • (Θ.B b).conjTranspose) = 1 :=
    mul_eq_one_comm.mp h_left
  -- B · Bᴴ = β • 1.
  have h_BBH : Θ.B b * (Θ.B b).conjTranspose =
      frobNormSq (Θ.B b) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have h_eq : (1 / frobNormSq (Θ.B b)) • (Θ.B b * (Θ.B b).conjTranspose) = 1 := by
      rw [← Matrix.mul_smul]; exact h_right
    rw [show Θ.B b * (Θ.B b).conjTranspose =
          frobNormSq (Θ.B b) • ((1 / frobNormSq (Θ.B b)) •
            (Θ.B b * (Θ.B b).conjTranspose)) from by
      rw [smul_smul, h_β_β_inv, one_smul]]
    rw [h_eq]
  -- Now apply rescaling.
  set sqβ := (Real.sqrt (frobNormSq (Θ.B b)).re : ℂ)
  have hβ_pos := frobNormSq_re_pos_of_ne_zero (Θ.B b) (hnd.B_pos b)
  have h_sqβ_pos := Real.sqrt_pos.mpr hβ_pos
  have h_sqβ_C_ne : sqβ ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt h_sqβ_pos)
  show (sqβ⁻¹ • Θ.B b) * (sqβ⁻¹ • Θ.B b).conjTranspose = 1
  rw [conjTranspose_real_inv_smul]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h_BBH, smul_smul]
  rw [show sqβ⁻¹ * sqβ⁻¹ * frobNormSq (Θ.B b) = 1 from ?_]
  · exact one_smul ℂ 1
  · rw [show (sqβ⁻¹ : ℂ) * (sqβ⁻¹ : ℂ) = (frobNormSq (Θ.B b) : ℂ)⁻¹ from ?_]
    · exact inv_mul_cancel₀ (hnd.B_pos b)
    · rw [← mul_inv]
      have h_sqβ_sq : sqβ * sqβ = (frobNormSq (Θ.B b) : ℂ) := by
        have h_sqβ_sq_R : (Real.sqrt (frobNormSq (Θ.B b)).re)^2 =
            (frobNormSq (Θ.B b)).re := Real.sq_sqrt (le_of_lt hβ_pos)
        rw [show sqβ * sqβ = ((Real.sqrt (frobNormSq (Θ.B b)).re)^2 : ℂ) from by
          push_cast; ring]
        rw [show ((Real.sqrt (frobNormSq (Θ.B b)).re)^2 : ℂ) =
            ((frobNormSq (Θ.B b)).re : ℂ) from by exact_mod_cast h_sqβ_sq_R]
        rw [← frobNormSq_eq_re_complex]
      rw [h_sqβ_sq]

/-! ## **κ=1 case discharge of `collinear_to_unitary_collinear`** -/

/-- **κ=1 case discharge.** Under PerfectCollinearity + Nondegenerate +
    Factorizes Θ f + κ=1 on support, the rescaled triple is a UnitaryCollinear
    factorisation. -/
theorem kappa_one_collinear_to_unitary_collinear (f : BinOp n)
    (hq : IsQuasigroup f) (Θ : HCParams n)
    (hcol : PerfectCollinearity Θ f) (hfeas : Factorizes Θ f)
    (hnd : Nondegenerate Θ)
    (hκ : ∀ a b : Fin n, kappaTriple Θ a b (f.op a b) = 1) :
    ∃ Θ' : HCParams n, UnitaryCollinear Θ' f := by
  refine ⟨rescaleByNorm Θ, ?_, ?_, ?_, ?_, ?_⟩
  · -- collinear : PerfectCollinearity (rescaleByNorm Θ) f
    exact PerfectCollinearity_rescaleByNorm Θ f hcol hnd
  · -- feasible : Factorizes (rescaleByNorm Θ) f
    exact Factorizes_rescaleByNorm_of_kappa_one Θ f hfeas hnd hκ
  · -- unitaryA
    exact unitary_rescaleByNorm_A_of_kappa_one Θ f hq hnd hcol hfeas hκ
  · -- unitaryB
    exact unitary_rescaleByNorm_B_of_kappa_one Θ f hq hnd hcol hfeas hκ
  · -- unitaryC
    exact unitary_rescaleByNorm_C_of_kappa_one Θ f hq hnd hcol hfeas hκ

/-! ## Active rank and the κ<1 case roadmap -/

/-- The active rank of `M`: the number of nonzero eigenvalues of `gramOf M`. -/
noncomputable def activeRank (M : Matrix (Fin n) (Fin n) ℂ) : ℕ :=
  Fintype.card {i : Fin n // (ActiveSubspaceGeneric.gramOf_isHermitian M).eigenvalues i ≠ 0}

/-- The active rank equals the rank of `gramOf M` (viewed as a matrix). -/
theorem activeRank_eq_rank (M : Matrix (Fin n) (Fin n) ℂ) :
    activeRank M = (ActiveSubspaceGeneric.gramOf M).rank :=
  ((ActiveSubspaceGeneric.gramOf_isHermitian M).rank_eq_card_non_zero_eigs).symm

/-- Active rank is bounded above by `n`. -/
theorem activeRank_le (M : Matrix (Fin n) (Fin n) ℂ) :
    activeRank M ≤ n := by
  unfold activeRank
  have h := Fintype.card_subtype_le
    (fun i : Fin n => (ActiveSubspaceGeneric.gramOf_isHermitian M).eigenvalues i ≠ 0)
  rw [Fintype.card_fin n] at h
  exact h

/-! ## Status: κ<1 case roadmap

The κ=1 case is fully mechanised via `kappa_one_collinear_to_unitary_collinear`.

The κ<1 case requires the manuscript's coordinated active-subspace argument:
  1. Decompose `ℂⁿ = V ⊕ V^⊥` where `V := range(X)` (active subspace,
     `dim V = activeRank X`).
  2. Show `A_a` maps `V → V` (since `range A_a ⊆ V` from
     `A_a A_aᴴ = α_a · X`), and similarly for `B_b, C_c`.
  3. On `V`, the rescaled `A_a/√α_a` is unitary (κ=1 case in dimension
     `activeRank X`).
  4. Build an auxiliary `Θ''` on `V^⊥` with the remaining trace structure
     (typically via leftRegularRep on a smaller index set).
  5. Lift back via direct sum: `Θ'.A a := A_a^V ⊕ Θ''.A a^{V^⊥}`.
  6. Verify Factorizes + PerfectCollinearity propagate through the
     direct sum.

This is a multi-day sub-project. The generic active-subspace machinery
in `ActiveSubspaceGeneric.lean` provides steps 1-3 (polar form `M = U·D·Q†`,
extended ONB, unitarity of Q). Steps 4-6 require new machinery for the
auxiliary structure and direct-sum verification. -/

end ActiveSubspaceConstruction

end
