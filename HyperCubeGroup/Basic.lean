/-
  HyperCubeGroup.Basic

  Core definitions for the HyperCube tensor factorization model.

  Mathematical setup:
  - (Q, ∘) is a finite quasigroup of order n
  - δ ∈ {0,1}^{n×n×n} is the structure tensor: δ_abc = 𝟙{a ∘ b = c}
  - A, B, C are families of n×n complex matrices indexed by Q
  - T_abc = (1/n) Tr(A_a B_b C_c) approximates δ
  - H(Θ) = Σ δ_abc (‖B_b C_c‖² + ‖C_c A_a‖² + ‖A_a B_b‖²)

  We use the normalized Frobenius inner product ⟨X, Y⟩ = (1/n) Tr(X† Y)
  so that ‖U‖² = 1 for any unitary U.
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.GroupTheory.Perm.Basic

open Matrix BigOperators Finset Complex ComplexConjugate

noncomputable section

/-! ## Quasigroup structure tensor -/

variable {n : ℕ} [NeZero n]

/-- A binary operation on Fin n, represented as a function. -/
structure BinOp (n : ℕ) where
  op : Fin n → Fin n → Fin n

/-- The structure tensor δ_abc = 𝟙{a ∘ b = c} for a binary operation. -/
def structureTensor (f : BinOp n) (a b c : Fin n) : ℂ :=
  if f.op a b = c then 1 else 0

/-- A binary operation is a quasigroup iff its Cayley table is a Latin square. -/
structure IsQuasigroup (f : BinOp n) : Prop where
  left_cancel : ∀ a : Fin n, Function.Bijective (f.op a)
  right_cancel : ∀ b : Fin n, Function.Bijective (fun a => f.op a b)

/-- A quasigroup is a group iff the operation is associative. -/
def IsAssociative (f : BinOp n) : Prop :=
  ∀ a b c : Fin n, f.op (f.op a b) c = f.op a (f.op b c)

/-- The support: set of triples (a,b,c) where a ∘ b = c. -/
def BinOp.support (f : BinOp n) : Finset (Fin n × Fin n × Fin n) :=
  Finset.univ.filter fun ⟨a, b, c⟩ => f.op a b = c

/-- |δ| = n² for any binary operation. -/
theorem support_card_eq (f : BinOp n) :
    f.support.card = n ^ 2 := by
  classical
  have key : f.support = (Finset.univ : Finset (Fin n × Fin n)).image
      (fun ab : Fin n × Fin n => (ab.1, ab.2, f.op ab.1 ab.2)) := by
    ext ⟨a, b, c⟩
    simp [BinOp.support, Finset.mem_filter, Finset.mem_image]
  rw [key, Finset.card_image_of_injective]
  · simp [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, sq]
  · intro ⟨a1, b1⟩ ⟨a2, b2⟩ h
    simp at h
    exact Prod.ext h.1 h.2.1

/-! ## HyperCube model parameters -/

/-- Parameter triple Θ = (A, B, C) where each is a family of n×n complex matrices. -/
structure HCParams (n : ℕ) where
  A : Fin n → Matrix (Fin n) (Fin n) ℂ
  B : Fin n → Matrix (Fin n) (Fin n) ℂ
  C : Fin n → Matrix (Fin n) (Fin n) ℂ

/-! ## Normalized Frobenius inner product and norm -/

/-- The normalized Frobenius inner product: ⟨X, Y⟩ = (1/n) Tr(X† Y). -/
def frobInner (X Y : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (1 / (n : ℂ)) * (X.conjTranspose * Y).trace

/-- The normalized Frobenius norm squared: ‖X‖² = ⟨X, X⟩. -/
def frobNormSq (X : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  frobInner X X

/-- Tr(X† X) is Hermitian, hence frobNormSq is real. -/
theorem frobNormSq_real (X : Matrix (Fin n) (Fin n) ℂ) :
    (frobNormSq X).im = 0 := by
  unfold frobNormSq frobInner
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [mul_im]
  have him_coeff : (1 / (n : ℂ)).im = 0 := by
    rw [one_div]
    simp [inv_im, normSq_natCast]
  have him_trace : (∑ i : Fin n, ∑ j : Fin n, star (X j i) * X j i).im = 0 := by
    rw [im_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [im_sum]
    apply Finset.sum_eq_zero
    intro j _
    simp only [← starRingEnd_apply]
    rw [← normSq_eq_conj_mul_self]
    exact ofReal_im _
  rw [him_coeff, him_trace]
  ring

/-- frobNormSq is nonneg (sum of |x_ij|²). -/
theorem frobNormSq_nonneg (X : Matrix (Fin n) (Fin n) ℂ) :
    (frobNormSq X).re ≥ 0 := by
  unfold frobNormSq frobInner
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [mul_re]
  have him_coeff : (1 / (n : ℂ)).im = 0 := by
    rw [one_div]
    simp [inv_im, normSq_natCast]
  have hre_coeff : (1 / (n : ℂ)).re ≥ 0 := by
    rw [one_div]
    simp only [inv_re, normSq_natCast, natCast_re]
    apply div_nonneg (Nat.cast_nonneg' n)
    exact mul_self_nonneg _
  have him_trace : (∑ i : Fin n, ∑ j : Fin n, star (X j i) * X j i).im = 0 := by
    rw [im_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [im_sum]
    apply Finset.sum_eq_zero
    intro j _
    simp only [← starRingEnd_apply]
    rw [← normSq_eq_conj_mul_self]
    exact ofReal_im _
  have hre_trace : (∑ i : Fin n, ∑ j : Fin n, star (X j i) * X j i).re ≥ 0 := by
    rw [re_sum]
    apply Finset.sum_nonneg
    intro i _
    rw [re_sum]
    apply Finset.sum_nonneg
    intro j _
    simp only [← starRingEnd_apply]
    rw [← normSq_eq_conj_mul_self]
    simp [normSq_nonneg]
  rw [him_coeff, him_trace]
  simp only [mul_zero, zero_mul, sub_zero, add_zero]
  exact mul_nonneg hre_coeff hre_trace

/-! ## HyperCube product tensor -/

/-- The HyperCube product: T_abc(Θ) = (1/n) Tr(A_a B_b C_c). -/
def hcProduct (Θ : HCParams n) (a b c : Fin n) : ℂ :=
  (1 / (n : ℂ)) * (Θ.A a * Θ.B b * Θ.C c).trace

omit [NeZero n] in
/-- T_abc as the Frobenius inner product ⟨A_a†, B_b C_c⟩. -/
theorem hcProduct_eq_frobInner (Θ : HCParams n) (a b c : Fin n) :
    hcProduct Θ a b c = frobInner (Θ.A a).conjTranspose (Θ.B b * Θ.C c) := by
  simp only [hcProduct, frobInner]
  congr 1
  rw [Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- Θ factorizes δ if T(Θ) = δ on all indices. -/
def Factorizes (Θ : HCParams n) (f : BinOp n) : Prop :=
  ∀ a b c : Fin n, hcProduct Θ a b c = structureTensor f a b c

/-- The feasible set F_δ. -/
def FeasibleSet (f : BinOp n) : Set (HCParams n) :=
  {Θ | Factorizes Θ f}

/-! ## Nondegeneracy assumption -/

/-- Every parameter slice has strictly positive norm. -/
structure Nondegenerate (Θ : HCParams n) : Prop where
  A_pos : ∀ a : Fin n, frobNormSq (Θ.A a) ≠ 0
  B_pos : ∀ b : Fin n, frobNormSq (Θ.B b) ≠ 0
  C_pos : ∀ c : Fin n, frobNormSq (Θ.C c) ≠ 0

/-! ## Jacobian-based objective H -/

/-- The Jacobian-based objective (Eq. 4):
    H(Θ) = Σ_{a,b,c} δ_abc (‖B_b C_c‖² + ‖C_c A_a‖² + ‖A_a B_b‖²). -/
def objective (Θ : HCParams n) (f : BinOp n) : ℂ :=
  ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
    structureTensor f a b c *
      (frobNormSq (Θ.B b * Θ.C c) +
       frobNormSq (Θ.C c * Θ.A a) +
       frobNormSq (Θ.A a * Θ.B b))

omit [NeZero n] in
/-- Equivalent formulation summing only over supported triples. -/
theorem objective_eq_sum_support (Θ : HCParams n) (f : BinOp n) :
    objective Θ f =
      ∑ a : Fin n, ∑ b : Fin n,
        (frobNormSq (Θ.B b * Θ.C (f.op a b)) +
         frobNormSq (Θ.C (f.op a b) * Θ.A a) +
         frobNormSq (Θ.A a * Θ.B b)) := by
  simp only [objective, structureTensor]
  congr 1; ext a; congr 1; ext b
  have key : ∀ c : Fin n, (if f.op a b = c then (1 : ℂ) else 0) *
      (frobNormSq (Θ.B b * Θ.C c) + frobNormSq (Θ.C c * Θ.A a) +
       frobNormSq (Θ.A a * Θ.B b)) =
    if f.op a b = c then
      (frobNormSq (Θ.B b * Θ.C c) + frobNormSq (Θ.C c * Θ.A a) +
       frobNormSq (Θ.A a * Θ.B b))
    else 0 := by intro c; split_ifs <;> simp
  simp_rw [key, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-! ## Gauge symmetries -/

/-- Gauge transformation for invertible U, V, W. -/
def gaugeTransform (Θ : HCParams n)
    (U V W : Matrix (Fin n) (Fin n) ℂ) : HCParams n where
  A := fun a => U * Θ.A a * V⁻¹
  B := fun b => V * Θ.B b * W⁻¹
  C := fun c => W * Θ.C c * U⁻¹

/-- The product T_abc is gauge-invariant (for invertible U, V, W).
    (UAV⁻¹)(VBW⁻¹)(WCU⁻¹) = U(ABC)U⁻¹, and Tr(MNM⁻¹) = Tr(N). -/
theorem hcProduct_gauge_invariant (Θ : HCParams n)
    (U V W : Matrix (Fin n) (Fin n) ℂ)
    (hU : IsUnit U) (hV : IsUnit V) (hW : IsUnit W)
    (a b c : Fin n) :
    hcProduct (gaugeTransform Θ U V W) a b c = hcProduct Θ a b c := by
  simp only [hcProduct, gaugeTransform]
  congr 1
  -- V⁻¹ * V = 1 and U * U⁻¹ = 1 using nonsing_inv
  have hVdet : IsUnit V.det := (isUnit_iff_isUnit_det (A := V)).mp hV
  have hWdet : IsUnit W.det := (isUnit_iff_isUnit_det (A := W)).mp hW
  have hUdet : IsUnit U.det := (isUnit_iff_isUnit_det (A := U)).mp hU
  have hVc : V⁻¹ * V = 1 := nonsing_inv_mul V hVdet
  have hWc : W⁻¹ * W = 1 := nonsing_inv_mul W hWdet
  -- Reassociate: (UAV⁻¹)(VBW⁻¹)(WCU⁻¹) = U(ABC)U⁻¹
  have key : U * Θ.A a * V⁻¹ * (V * Θ.B b * W⁻¹) * (W * Θ.C c * U⁻¹) =
      U * (Θ.A a * Θ.B b * Θ.C c) * U⁻¹ := by
    have hUmul : U * U⁻¹ = 1 := mul_nonsing_inv U hUdet
    -- Use simp with mul_assoc to flatten, then cancel V⁻¹V and W⁻¹W
    simp only [mul_assoc]
    -- After full right-association, we have:
    -- U * (A * (V⁻¹ * (V * (B * (W⁻¹ * (W * (C * U⁻¹)))))))
    -- = U * (A * (B * (C * U⁻¹)))
    rw [← mul_assoc V⁻¹ V, hVc, one_mul,
        ← mul_assoc W⁻¹ W, hWc, one_mul]
  rw [key, mul_assoc U _ U⁻¹, trace_mul_comm U,
      mul_assoc, nonsing_inv_mul U hUdet, mul_one]

/-- Isotopy equivariance: permuting indices preserves T. -/
def isotopeTransform (Θ : HCParams n) (φ ψ χ : Equiv.Perm (Fin n)) : HCParams n where
  A := fun a => Θ.A (φ a)
  B := fun b => Θ.B (ψ b)
  C := fun c => Θ.C (χ c)

omit [NeZero n] in
theorem hcProduct_isotope_equiv (Θ : HCParams n)
    (φ ψ χ : Equiv.Perm (Fin n)) (a b c : Fin n) :
    hcProduct (isotopeTransform Θ φ ψ χ) a b c =
    hcProduct Θ (φ a) (ψ b) (χ c) := by
  simp [hcProduct, isotopeTransform]

end
