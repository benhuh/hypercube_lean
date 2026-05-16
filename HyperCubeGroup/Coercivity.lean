/-
  HyperCubeGroup.Coercivity

  Coercivity bounds and gauge stability from Manuscript Appendix F.
  This is Tier 3B in the README roadmap and the largest remaining
  mechanisation piece.

  Scope:
    * Laplacian Hessian of the objective `ℋ(Θ)` at optimal points.
    * Scaling potentials: bounds on `ℋ(Θ)` along the gauge orbit.
    * Coefficient graph spectral analysis: eigenvalues of the
      Laplacian of the structure graph control coercivity.
    * Quadratic lower bound: `ℋ(Θ) - 3n² ≥ c · dist(Θ, Θ_opt)²` near
      the optimal manifold (modulo gauge).

  Status: scaffold only. The full mechanisation is roughly 1500-2500
  lines and best approached as its own focused sub-project after the
  Tikhonov existence theorem (Tier 3A) is in place.

  Why it matters: the manuscript's Tikhonov existence theorem
  (`thm:app_regularized_existence`, Theorem 27) and the empirical
  coercivity discussion in Appendix F use these bounds to argue that
  gradient descent on `H` converges globally to the optimal manifold
  (no spurious local minima beyond gauge orbits). Without coercivity,
  even with global minimum existence (Tier 3A), optimisation could
  stall on flat directions or saddle structures.
-/

import HyperCubeGroup.Basic
import HyperCubeGroup.Decomposition
import HyperCubeGroup.Abelian
import HyperCubeGroup.Tikhonov

open Matrix BigOperators Complex

noncomputable section

namespace Coercivity

variable {n : ℕ} [NeZero n]

/-! ## Gauge action: per-slot complex scaling -/

/-- The gauge action: scale each slice by a per-slot complex factor. -/
noncomputable def gaugeAction (sA sB sC : Fin n → ℂ) (Θ : HCParams n) : HCParams n :=
  ⟨fun a => sA a • Θ.A a,
   fun b => sB b • Θ.B b,
   fun c => sC c • Θ.C c⟩

/-- The trivial gauge action (all factors = 1) is the identity. -/
@[simp] theorem gaugeAction_one (Θ : HCParams n) :
    gaugeAction (fun _ => (1 : ℂ)) (fun _ => 1) (fun _ => 1) Θ = Θ := by
  unfold gaugeAction
  cases Θ
  simp [one_smul]

/-- `frobNormSq` under gauge action: scales by `|s_a|²`. -/
theorem frobNormSq_gaugeAction_A (sA sB sC : Fin n → ℂ) (Θ : HCParams n) (a : Fin n) :
    frobNormSq ((gaugeAction sA sB sC Θ).A a) =
    sA a * starRingEnd ℂ (sA a) * frobNormSq (Θ.A a) := by
  show frobNormSq (sA a • Θ.A a) = _
  rw [frobNormSq_smul]

theorem frobNormSq_gaugeAction_B (sA sB sC : Fin n → ℂ) (Θ : HCParams n) (b : Fin n) :
    frobNormSq ((gaugeAction sA sB sC Θ).B b) =
    sB b * starRingEnd ℂ (sB b) * frobNormSq (Θ.B b) := by
  show frobNormSq (sB b • Θ.B b) = _
  rw [frobNormSq_smul]

theorem frobNormSq_gaugeAction_C (sA sB sC : Fin n → ℂ) (Θ : HCParams n) (c : Fin n) :
    frobNormSq ((gaugeAction sA sB sC Θ).C c) =
    sC c * starRingEnd ℂ (sC c) * frobNormSq (Θ.C c) := by
  show frobNormSq (sC c • Θ.C c) = _
  rw [frobNormSq_smul]

/-- `hcProduct` under gauge action: scales by `s_A a · s_B b · s_C c`. -/
theorem hcProduct_gaugeAction (sA sB sC : Fin n → ℂ) (Θ : HCParams n) (a b c : Fin n) :
    hcProduct (gaugeAction sA sB sC Θ) a b c =
    (sA a * sB b * sC c) * hcProduct Θ a b c := by
  unfold hcProduct
  show (1 / (n : ℂ)) *
      ((sA a • Θ.A a) * (sB b • Θ.B b) * (sC c • Θ.C c)).trace = _
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul]
  simp only [Matrix.trace_smul, smul_eq_mul]
  ring

/-- Gauge action preserves `Factorizes` if and only if `s_A a · s_B b · s_C c = 1`
    on support. -/
theorem factorizes_gaugeAction_iff (sA sB sC : Fin n → ℂ) (Θ : HCParams n) (f : BinOp n)
    (hfeas : Factorizes Θ f) :
    Factorizes (gaugeAction sA sB sC Θ) f ↔
    ∀ a b : Fin n, sA a * sB b * sC (f.op a b) = 1 := by
  constructor
  · intro h_feas a b
    have h := h_feas a b (f.op a b)
    rw [hcProduct_gaugeAction, structureTensor, if_pos rfl] at h
    have hT : hcProduct Θ a b (f.op a b) = 1 := by
      have := hfeas a b (f.op a b)
      rwa [structureTensor, if_pos rfl] at this
    rw [hT, mul_one] at h
    exact h
  · intro h_unit a b c
    rw [hcProduct_gaugeAction]
    by_cases hc : c = f.op a b
    · subst hc
      have hT : hcProduct Θ a b (f.op a b) = 1 := by
        have := hfeas a b (f.op a b)
        rwa [structureTensor, if_pos rfl] at this
      rw [hT, mul_one]
      rw [structureTensor, if_pos rfl]
      exact h_unit a b
    · have hT : hcProduct Θ a b c = 0 := by
        have := hfeas a b c
        rwa [structureTensor, if_neg (Ne.symm hc)] at this
      rw [hT, mul_zero]
      rw [structureTensor, if_neg (Ne.symm hc)]

/-! ## Objective under gauge action -/

/-- The product `B · C` under gauge action: `(s_B • B) · (s_C • C) = (s_B · s_C) • (B · C)`. -/
private lemma BC_gaugeAction (sA sB sC : Fin n → ℂ) (Θ : HCParams n) (b c : Fin n) :
    (gaugeAction sA sB sC Θ).B b * (gaugeAction sA sB sC Θ).C c =
    (sB b * sC c) • (Θ.B b * Θ.C c) := by
  show (sB b • Θ.B b) * (sC c • Θ.C c) = _
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

private lemma CA_gaugeAction (sA sB sC : Fin n → ℂ) (Θ : HCParams n) (c a : Fin n) :
    (gaugeAction sA sB sC Θ).C c * (gaugeAction sA sB sC Θ).A a =
    (sC c * sA a) • (Θ.C c * Θ.A a) := by
  show (sC c • Θ.C c) * (sA a • Θ.A a) = _
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

private lemma AB_gaugeAction (sA sB sC : Fin n → ℂ) (Θ : HCParams n) (a b : Fin n) :
    (gaugeAction sA sB sC Θ).A a * (gaugeAction sA sB sC Θ).B b =
    (sA a * sB b) • (Θ.A a * Θ.B b) := by
  show (sA a • Θ.A a) * (sB b • Θ.B b) = _
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

/-- `frobNormSq` of `(s • M)`: equals `|s|² · frobNormSq M`. -/
private lemma frobNormSq_smul_eq (s : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
    frobNormSq (s • M) = (s * starRingEnd ℂ s) * frobNormSq M := by
  rw [frobNormSq_smul]

/-- The objective under gauge action: each Frobenius² term gets scaled
    by the modulus-squared product of the relevant gauge factors. -/
theorem objective_gaugeAction (sA sB sC : Fin n → ℂ) (Θ : HCParams n) (f : BinOp n) :
    objective (gaugeAction sA sB sC Θ) f =
    ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
      structureTensor f a b c *
        ((sB b * starRingEnd ℂ (sB b)) * (sC c * starRingEnd ℂ (sC c)) *
            frobNormSq (Θ.B b * Θ.C c) +
         (sC c * starRingEnd ℂ (sC c)) * (sA a * starRingEnd ℂ (sA a)) *
            frobNormSq (Θ.C c * Θ.A a) +
         (sA a * starRingEnd ℂ (sA a)) * (sB b * starRingEnd ℂ (sB b)) *
            frobNormSq (Θ.A a * Θ.B b)) := by
  unfold objective
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  rw [BC_gaugeAction, CA_gaugeAction, AB_gaugeAction]
  rw [frobNormSq_smul_eq, frobNormSq_smul_eq, frobNormSq_smul_eq]
  simp only [map_mul]
  ring

/-- If all gauge factors have unit modulus (|s_X|² = 1), the objective is invariant. -/
theorem objective_invariant_under_unit_gauge (sA sB sC : Fin n → ℂ) (Θ : HCParams n)
    (f : BinOp n)
    (hA : ∀ a : Fin n, sA a * starRingEnd ℂ (sA a) = 1)
    (hB : ∀ b : Fin n, sB b * starRingEnd ℂ (sB b) = 1)
    (hC : ∀ c : Fin n, sC c * starRingEnd ℂ (sC c) = 1) :
    objective (gaugeAction sA sB sC Θ) f = objective Θ f := by
  rw [objective_gaugeAction]
  unfold objective
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  rw [hA a, hB b, hC c]
  ring

/-! ## Uniform scaling and homogeneity -/

/-- Uniform scaling: multiply every slice of `Θ` by the same complex `t`. -/
noncomputable def uniformScale (t : ℂ) (Θ : HCParams n) : HCParams n :=
  gaugeAction (fun _ => t) (fun _ => t) (fun _ => t) Θ

/-- Trivial uniform scaling (`t = 1`) is the identity. -/
@[simp] theorem uniformScale_one (Θ : HCParams n) :
    uniformScale 1 Θ = Θ :=
  gaugeAction_one Θ

/-- Under uniform scaling by `t`, `frobNormSq` of every slice scales by `|t|²`. -/
theorem frobNormSq_uniformScale_A (t : ℂ) (Θ : HCParams n) (a : Fin n) :
    frobNormSq ((uniformScale t Θ).A a) =
    t * starRingEnd ℂ t * frobNormSq (Θ.A a) :=
  frobNormSq_gaugeAction_A _ _ _ _ _

/-- Under uniform scaling by `t`, `hcProduct` scales by `t³`. -/
theorem hcProduct_uniformScale (t : ℂ) (Θ : HCParams n) (a b c : Fin n) :
    hcProduct (uniformScale t Θ) a b c = t ^ 3 * hcProduct Θ a b c := by
  rw [uniformScale, hcProduct_gaugeAction]
  ring

/-- **Homogeneity of degree 4.** Under uniform scaling by `t`, the
    objective scales by `(t · star t)²`. -/
theorem objective_uniformScale (t : ℂ) (Θ : HCParams n) (f : BinOp n) :
    objective (uniformScale t Θ) f =
    (t * starRingEnd ℂ t) ^ 2 * objective Θ f := by
  rw [uniformScale, objective_gaugeAction]
  unfold objective
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- For positive real `t`, `H(t·Θ).re = t⁴ · ℋ(Θ).re`. -/
theorem objective_re_uniformScale_real (t : ℝ) (Θ : HCParams n) (f : BinOp n) :
    (objective (uniformScale (t : ℂ) Θ) f).re = t ^ 4 * (objective Θ f).re := by
  rw [objective_uniformScale]
  -- ((t : ℂ) * conj (t : ℂ))² = (t · t)² = t⁴ (for real t).
  have h_star : starRingEnd ℂ ((t : ℂ)) = (t : ℂ) := Complex.conj_ofReal t
  rw [h_star]
  rw [show ((t : ℂ) * (t : ℂ)) ^ 2 = ((t ^ 4 : ℝ) : ℂ) from by push_cast; ring]
  rw [Complex.mul_re]
  show t ^ 4 * (objective Θ f).re - 0 * (objective Θ f).im = t ^ 4 * (objective Θ f).re
  ring

/-! ## Unitary conjugation gauge -/

/-- The unitary conjugation gauge: conjugate every slice by a fixed unitary `U`. -/
noncomputable def unitaryConjAction (U : Matrix (Fin n) (Fin n) ℂ) (Θ : HCParams n) :
    HCParams n :=
  ⟨fun a => U * Θ.A a * U.conjTranspose,
   fun b => U * Θ.B b * U.conjTranspose,
   fun c => U * Θ.C c * U.conjTranspose⟩

/-- Trivial unitary conjugation (`U = 1`) is the identity. -/
@[simp] theorem unitaryConjAction_one (Θ : HCParams n) :
    unitaryConjAction 1 Θ = Θ := by
  unfold unitaryConjAction
  cases Θ
  simp

/-- Under unitary conjugation, the trace product `Tr(A · B · C)` is invariant. -/
theorem hcProduct_unitaryConjAction (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1) (Θ : HCParams n) (a b c : Fin n) :
    hcProduct (unitaryConjAction U Θ) a b c = hcProduct Θ a b c := by
  unfold hcProduct unitaryConjAction
  congr 1
  show ((U * Θ.A a * U.conjTranspose) * (U * Θ.B b * U.conjTranspose) *
        (U * Θ.C c * U.conjTranspose)).trace = _
  have hU' : U.conjTranspose * U = 1 := mul_eq_one_comm.mp hU
  -- Use trace cyclicity: Tr(U · X · Uᴴ) = Tr(Uᴴ · U · X) = Tr(X) when Uᴴ U = 1.
  -- First simplify (UAUᴴ)(UBUᴴ)(UCUᴴ) by collapsing UᴴU's.
  have step1 : U * Θ.A a * U.conjTranspose * (U * Θ.B b * U.conjTranspose) =
      U * (Θ.A a * Θ.B b) * U.conjTranspose := by
    calc U * Θ.A a * U.conjTranspose * (U * Θ.B b * U.conjTranspose)
        = U * Θ.A a * (U.conjTranspose * U) * Θ.B b * U.conjTranspose := by
          rw [show U * Θ.A a * U.conjTranspose * (U * Θ.B b * U.conjTranspose) =
              U * Θ.A a * U.conjTranspose * U * Θ.B b * U.conjTranspose from by
            rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]]
          rw [Matrix.mul_assoc (U * Θ.A a) U.conjTranspose U]
      _ = U * Θ.A a * 1 * Θ.B b * U.conjTranspose := by rw [hU']
      _ = U * (Θ.A a * Θ.B b) * U.conjTranspose := by
          rw [Matrix.mul_one, Matrix.mul_assoc U _ _]
  rw [step1]
  have step2 : U * (Θ.A a * Θ.B b) * U.conjTranspose * (U * Θ.C c * U.conjTranspose) =
      U * (Θ.A a * Θ.B b * Θ.C c) * U.conjTranspose := by
    calc U * (Θ.A a * Θ.B b) * U.conjTranspose * (U * Θ.C c * U.conjTranspose)
        = U * (Θ.A a * Θ.B b) * (U.conjTranspose * U) * Θ.C c * U.conjTranspose := by
          rw [show U * (Θ.A a * Θ.B b) * U.conjTranspose * (U * Θ.C c * U.conjTranspose) =
              U * (Θ.A a * Θ.B b) * U.conjTranspose * U * Θ.C c * U.conjTranspose from by
            rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]]
          rw [Matrix.mul_assoc (U * (Θ.A a * Θ.B b)) U.conjTranspose U]
      _ = U * (Θ.A a * Θ.B b) * 1 * Θ.C c * U.conjTranspose := by rw [hU']
      _ = U * (Θ.A a * Θ.B b * Θ.C c) * U.conjTranspose := by
          rw [Matrix.mul_one, Matrix.mul_assoc U _ _]
  rw [step2]
  -- Tr(U · X · Uᴴ) = Tr(Uᴴ · U · X) = Tr(X) (cyclic + UᴴU = 1).
  rw [Matrix.trace_mul_comm]
  rw [show U.conjTranspose * (U * (Θ.A a * Θ.B b * Θ.C c)) =
        (U.conjTranspose * U) * (Θ.A a * Θ.B b * Θ.C c) from
      (Matrix.mul_assoc _ _ _).symm]
  rw [hU', Matrix.one_mul]

/-! ## frobNormSq invariance under unitary conjugation -/

/-- `frobNormSq` is invariant under unitary conjugation. -/
theorem frobNormSq_unitaryConj (U M : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1) :
    frobNormSq (U * M * U.conjTranspose) = frobNormSq M := by
  have hU' : U.conjTranspose * U = 1 := mul_eq_one_comm.mp hU
  -- Step 1: frobNormSq (U·M·Uᴴ) = frobNormSq (U·M) by right-invariance.
  -- Right-invariance needs V·Vᴴ = 1 for the right factor V = Uᴴ.
  -- (Uᴴ)·(Uᴴ)ᴴ = Uᴴ·U = 1 (which is hU').
  have h_step1 : frobNormSq ((U * M) * U.conjTranspose) = frobNormSq (U * M) :=
    frobNormSq_unitary_mul_right (U * M) U.conjTranspose
      (by rw [Matrix.conjTranspose_conjTranspose]; exact hU')
  rw [show U * M * U.conjTranspose = (U * M) * U.conjTranspose from rfl]
  rw [h_step1]
  -- Step 2: frobNormSq (U·M) = frobNormSq M by left-invariance.
  exact frobNormSq_unitary_mul_left U M hU'

/-- `frobNormSq` of slice products is invariant under unitary conjugation:
    `‖U·B·Uᴴ · U·C·Uᴴ‖² = ‖B·C‖²`. -/
theorem frobNormSq_BC_unitaryConj (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1) (Θ : HCParams n) (b c : Fin n) :
    frobNormSq ((unitaryConjAction U Θ).B b * (unitaryConjAction U Θ).C c) =
    frobNormSq (Θ.B b * Θ.C c) := by
  show frobNormSq (U * Θ.B b * U.conjTranspose * (U * Θ.C c * U.conjTranspose)) = _
  have hU' : U.conjTranspose * U = 1 := mul_eq_one_comm.mp hU
  rw [show U * Θ.B b * U.conjTranspose * (U * Θ.C c * U.conjTranspose) =
      U * (Θ.B b * Θ.C c) * U.conjTranspose from by
    calc U * Θ.B b * U.conjTranspose * (U * Θ.C c * U.conjTranspose)
        = U * Θ.B b * (U.conjTranspose * U) * Θ.C c * U.conjTranspose := by
          rw [show U * Θ.B b * U.conjTranspose * (U * Θ.C c * U.conjTranspose) =
              U * Θ.B b * U.conjTranspose * U * Θ.C c * U.conjTranspose from by
            rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]]
          rw [Matrix.mul_assoc (U * Θ.B b) U.conjTranspose U]
      _ = U * Θ.B b * 1 * Θ.C c * U.conjTranspose := by rw [hU']
      _ = U * (Θ.B b * Θ.C c) * U.conjTranspose := by
          rw [Matrix.mul_one, Matrix.mul_assoc U _ _]]
  exact frobNormSq_unitaryConj U (Θ.B b * Θ.C c) hU

theorem frobNormSq_CA_unitaryConj (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1) (Θ : HCParams n) (c a : Fin n) :
    frobNormSq ((unitaryConjAction U Θ).C c * (unitaryConjAction U Θ).A a) =
    frobNormSq (Θ.C c * Θ.A a) := by
  show frobNormSq (U * Θ.C c * U.conjTranspose * (U * Θ.A a * U.conjTranspose)) = _
  have hU' : U.conjTranspose * U = 1 := mul_eq_one_comm.mp hU
  rw [show U * Θ.C c * U.conjTranspose * (U * Θ.A a * U.conjTranspose) =
      U * (Θ.C c * Θ.A a) * U.conjTranspose from by
    calc U * Θ.C c * U.conjTranspose * (U * Θ.A a * U.conjTranspose)
        = U * Θ.C c * (U.conjTranspose * U) * Θ.A a * U.conjTranspose := by
          rw [show U * Θ.C c * U.conjTranspose * (U * Θ.A a * U.conjTranspose) =
              U * Θ.C c * U.conjTranspose * U * Θ.A a * U.conjTranspose from by
            rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]]
          rw [Matrix.mul_assoc (U * Θ.C c) U.conjTranspose U]
      _ = U * Θ.C c * 1 * Θ.A a * U.conjTranspose := by rw [hU']
      _ = U * (Θ.C c * Θ.A a) * U.conjTranspose := by
          rw [Matrix.mul_one, Matrix.mul_assoc U _ _]]
  exact frobNormSq_unitaryConj U (Θ.C c * Θ.A a) hU

theorem frobNormSq_AB_unitaryConj (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1) (Θ : HCParams n) (a b : Fin n) :
    frobNormSq ((unitaryConjAction U Θ).A a * (unitaryConjAction U Θ).B b) =
    frobNormSq (Θ.A a * Θ.B b) := by
  show frobNormSq (U * Θ.A a * U.conjTranspose * (U * Θ.B b * U.conjTranspose)) = _
  have hU' : U.conjTranspose * U = 1 := mul_eq_one_comm.mp hU
  rw [show U * Θ.A a * U.conjTranspose * (U * Θ.B b * U.conjTranspose) =
      U * (Θ.A a * Θ.B b) * U.conjTranspose from by
    calc U * Θ.A a * U.conjTranspose * (U * Θ.B b * U.conjTranspose)
        = U * Θ.A a * (U.conjTranspose * U) * Θ.B b * U.conjTranspose := by
          rw [show U * Θ.A a * U.conjTranspose * (U * Θ.B b * U.conjTranspose) =
              U * Θ.A a * U.conjTranspose * U * Θ.B b * U.conjTranspose from by
            rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]]
          rw [Matrix.mul_assoc (U * Θ.A a) U.conjTranspose U]
      _ = U * Θ.A a * 1 * Θ.B b * U.conjTranspose := by rw [hU']
      _ = U * (Θ.A a * Θ.B b) * U.conjTranspose := by
          rw [Matrix.mul_one, Matrix.mul_assoc U _ _]]
  exact frobNormSq_unitaryConj U (Θ.A a * Θ.B b) hU

/-- The objective is invariant under unitary conjugation. -/
theorem objective_unitaryConjAction (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1) (Θ : HCParams n) (f : BinOp n) :
    objective (unitaryConjAction U Θ) f = objective Θ f := by
  unfold objective
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  rw [frobNormSq_BC_unitaryConj U hU,
      frobNormSq_CA_unitaryConj U hU,
      frobNormSq_AB_unitaryConj U hU]

/-! ## Uniform scaling and the feasible manifold -/

/-- `uniformScale t` preserves `Factorizes` if and only if `t³ = 1`
    (the gauge-allowed scalings are cube roots of unity). -/
theorem factorizes_uniformScale_iff (t : ℂ) (Θ : HCParams n) (f : BinOp n)
    (hfeas : Factorizes Θ f) (hne : (∃ a b : Fin n, hcProduct Θ a b (f.op a b) = 1)) :
    Factorizes (uniformScale t Θ) f ↔ t ^ 3 = 1 := by
  constructor
  · intro h_feas
    -- Pick witness (a, b) with hcProduct Θ a b (f.op a b) = 1.
    obtain ⟨a, b, hT⟩ := hne
    have h := h_feas a b (f.op a b)
    rw [hcProduct_uniformScale, structureTensor, if_pos rfl, hT, mul_one] at h
    exact h
  · intro h_t3 a b c
    rw [hcProduct_uniformScale]
    by_cases hc : c = f.op a b
    · subst hc
      have hT : hcProduct Θ a b (f.op a b) = 1 := by
        have := hfeas a b (f.op a b)
        rwa [structureTensor, if_pos rfl] at this
      rw [hT, mul_one, h_t3, structureTensor, if_pos rfl]
    · have hT : hcProduct Θ a b c = 0 := by
        have := hfeas a b c
        rwa [structureTensor, if_neg (Ne.symm hc)] at this
      rw [hT, mul_zero, structureTensor, if_neg (Ne.symm hc)]

/-- For non-degenerate `Θ` with `Factorizes`, the trace product is `1` on
    every support triple, so the witness for `factorizes_uniformScale_iff`
    is automatic. -/
theorem hcProduct_eq_one_on_support (Θ : HCParams n) (f : BinOp n)
    (hfeas : Factorizes Θ f) (a b : Fin n) :
    hcProduct Θ a b (f.op a b) = 1 := by
  have := hfeas a b (f.op a b)
  rwa [structureTensor, if_pos rfl] at this

/-! ## Composition properties of gauge actions -/

/-- `uniformScale` is multiplicative: `uniformScale (s · t) = uniformScale s ∘ uniformScale t`. -/
theorem uniformScale_mul (s t : ℂ) (Θ : HCParams n) :
    uniformScale (s * t) Θ = uniformScale s (uniformScale t Θ) := by
  unfold uniformScale gaugeAction
  cases Θ
  simp only [HCParams.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  all_goals
    funext _
    rw [smul_smul]

/-- `unitaryConjAction` composes naturally: conjugating by `U₁` then `U₂`
    is conjugating by `U₂ · U₁`. -/
theorem unitaryConjAction_mul (U₁ U₂ : Matrix (Fin n) (Fin n) ℂ) (Θ : HCParams n) :
    unitaryConjAction U₂ (unitaryConjAction U₁ Θ) = unitaryConjAction (U₂ * U₁) Θ := by
  unfold unitaryConjAction
  cases Θ
  simp only [HCParams.mk.injEq, Matrix.conjTranspose_mul]
  refine ⟨?_, ?_, ?_⟩
  all_goals
    funext _
    -- LHS: U₂ * (U₁ * M * U₁ᴴ) * U₂ᴴ
    -- RHS: (U₂ * U₁) * M * (U₁ᴴ * U₂ᴴ)
    -- These are equal by associativity (both are U₂·U₁·M·U₁ᴴ·U₂ᴴ).
    simp only [Matrix.mul_assoc]

/-! ## Gauge orbit -/

/-- The gauge orbit of `Θ` under the unitary conjugation action. -/
def unitaryGaugeOrbit (Θ : HCParams n) : Set (HCParams n) :=
  {Ψ | ∃ U : Matrix (Fin n) (Fin n) ℂ, U * U.conjTranspose = 1 ∧ Ψ = unitaryConjAction U Θ}

/-- The orbit always contains `Θ` itself (via `U = 1`). -/
theorem mem_unitaryGaugeOrbit_self (Θ : HCParams n) :
    Θ ∈ unitaryGaugeOrbit Θ := by
  refine ⟨1, ?_, ?_⟩
  · simp
  · rw [unitaryConjAction_one]

/-- Membership in the orbit is symmetric. -/
theorem unitaryGaugeOrbit_symm {Θ Ψ : HCParams n} (h : Ψ ∈ unitaryGaugeOrbit Θ) :
    Θ ∈ unitaryGaugeOrbit Ψ := by
  obtain ⟨U, hU, hΨ⟩ := h
  have hU' : U.conjTranspose * U = 1 := mul_eq_one_comm.mp hU
  refine ⟨U.conjTranspose, ?_, ?_⟩
  · rw [Matrix.conjTranspose_conjTranspose]; exact hU'
  · rw [hΨ, unitaryConjAction_mul]
    rw [show U.conjTranspose * U = 1 from hU']
    rw [unitaryConjAction_one]

/-- The objective is constant on a unitary gauge orbit. -/
theorem objective_constant_on_orbit (Θ Ψ : HCParams n) (f : BinOp n)
    (h : Ψ ∈ unitaryGaugeOrbit Θ) :
    objective Ψ f = objective Θ f := by
  obtain ⟨U, hU, hΨ⟩ := h
  rw [hΨ]
  exact objective_unitaryConjAction U hU Θ f

/-- Gauge orbit membership is transitive. -/
theorem unitaryGaugeOrbit_trans {Θ Ψ Φ : HCParams n}
    (h1 : Ψ ∈ unitaryGaugeOrbit Θ) (h2 : Φ ∈ unitaryGaugeOrbit Ψ) :
    Φ ∈ unitaryGaugeOrbit Θ := by
  obtain ⟨U₁, hU₁, hΨ⟩ := h1
  obtain ⟨U₂, hU₂, hΦ⟩ := h2
  -- Φ = U₂ · Ψ · U₂ᴴ = U₂ · (U₁ · Θ · U₁ᴴ) · U₂ᴴ = (U₂ · U₁) · Θ · (U₂ · U₁)ᴴ.
  refine ⟨U₂ * U₁, ?_, ?_⟩
  · -- (U₂ · U₁) · (U₂ · U₁)ᴴ = U₂ · U₁ · U₁ᴴ · U₂ᴴ = U₂ · 1 · U₂ᴴ = 1.
    rw [Matrix.conjTranspose_mul]
    rw [show U₂ * U₁ * (U₁.conjTranspose * U₂.conjTranspose) =
        U₂ * (U₁ * U₁.conjTranspose) * U₂.conjTranspose from by
      simp only [Matrix.mul_assoc]]
    rw [hU₁, Matrix.mul_one, hU₂]
  · rw [hΦ, hΨ, unitaryConjAction_mul]

/-- `frobNormSq` of each slice is constant on a unitary gauge orbit (A-side). -/
theorem frobNormSq_A_constant_on_orbit (Θ Ψ : HCParams n)
    (h : Ψ ∈ unitaryGaugeOrbit Θ) (a : Fin n) :
    frobNormSq (Ψ.A a) = frobNormSq (Θ.A a) := by
  obtain ⟨U, hU, hΨ⟩ := h
  rw [hΨ]
  show frobNormSq (U * Θ.A a * U.conjTranspose) = _
  exact frobNormSq_unitaryConj U (Θ.A a) hU

/-- `frobNormSq` of each slice is constant on a unitary gauge orbit (B-side). -/
theorem frobNormSq_B_constant_on_orbit (Θ Ψ : HCParams n)
    (h : Ψ ∈ unitaryGaugeOrbit Θ) (b : Fin n) :
    frobNormSq (Ψ.B b) = frobNormSq (Θ.B b) := by
  obtain ⟨U, hU, hΨ⟩ := h
  rw [hΨ]
  show frobNormSq (U * Θ.B b * U.conjTranspose) = _
  exact frobNormSq_unitaryConj U (Θ.B b) hU

/-- `frobNormSq` of each slice is constant on a unitary gauge orbit (C-side). -/
theorem frobNormSq_C_constant_on_orbit (Θ Ψ : HCParams n)
    (h : Ψ ∈ unitaryGaugeOrbit Θ) (c : Fin n) :
    frobNormSq (Ψ.C c) = frobNormSq (Θ.C c) := by
  obtain ⟨U, hU, hΨ⟩ := h
  rw [hΨ]
  show frobNormSq (U * Θ.C c * U.conjTranspose) = _
  exact frobNormSq_unitaryConj U (Θ.C c) hU

/-- The unitary gauge orbit preserves the `Factorizes` property. -/
theorem factorizes_unitaryConjAction (Θ : HCParams n) (f : BinOp n)
    (hfeas : Factorizes Θ f) (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1) :
    Factorizes (unitaryConjAction U Θ) f := by
  intro a b c
  rw [hcProduct_unitaryConjAction U hU Θ a b c]
  exact hfeas a b c

/-- The unitary gauge orbit is contained in the feasible set when Theta is feasible. -/
theorem feasible_unitaryGaugeOrbit (Θ : HCParams n) (f : BinOp n)
    (hfeas : Factorizes Θ f) (Ψ : HCParams n) (h : Ψ ∈ unitaryGaugeOrbit Θ) :
    Factorizes Ψ f := by
  obtain ⟨U, hU, hΨ⟩ := h
  rw [hΨ]
  exact factorizes_unitaryConjAction Θ f hfeas U hU

/-! ## kappaTriple invariance -/

/-- `kappaTriple` is invariant under unitary conjugation. -/
theorem kappaTriple_unitaryConjAction (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1) (Θ : HCParams n) (a b c : Fin n) :
    kappaTriple (unitaryConjAction U Θ) a b c = kappaTriple Θ a b c := by
  unfold kappaTriple
  -- Numerator: frobNormSq slices invariant under unitary conjugation.
  have hA : frobNormSq ((unitaryConjAction U Θ).A a) = frobNormSq (Θ.A a) := by
    show frobNormSq (U * Θ.A a * U.conjTranspose) = _
    exact frobNormSq_unitaryConj U (Θ.A a) hU
  have hB : frobNormSq ((unitaryConjAction U Θ).B b) = frobNormSq (Θ.B b) := by
    show frobNormSq (U * Θ.B b * U.conjTranspose) = _
    exact frobNormSq_unitaryConj U (Θ.B b) hU
  have hC : frobNormSq ((unitaryConjAction U Θ).C c) = frobNormSq (Θ.C c) := by
    show frobNormSq (U * Θ.C c * U.conjTranspose) = _
    exact frobNormSq_unitaryConj U (Θ.C c) hU
  -- Denominator: hcProduct invariant under unitary conjugation.
  have hT : hcProduct (unitaryConjAction U Θ) a b c = hcProduct Θ a b c :=
    hcProduct_unitaryConjAction U hU Θ a b c
  rw [hA, hB, hC, hT]

/-- `kappaTriple` is constant on the unitary gauge orbit. -/
theorem kappaTriple_constant_on_orbit (Θ Ψ : HCParams n)
    (h : Ψ ∈ unitaryGaugeOrbit Θ) (a b c : Fin n) :
    kappaTriple Ψ a b c = kappaTriple Θ a b c := by
  obtain ⟨U, hU, hΨ⟩ := h
  rw [hΨ]
  exact kappaTriple_unitaryConjAction U hU Θ a b c

/-! ## Gauge orbit as an equivalence relation -/

/-- The unitary gauge action induces an equivalence relation on `HCParams n`. -/
def unitaryGaugeSetoid : Setoid (HCParams n) where
  r Θ Ψ := Ψ ∈ unitaryGaugeOrbit Θ
  iseqv := ⟨mem_unitaryGaugeOrbit_self,
            unitaryGaugeOrbit_symm,
            fun h₁ h₂ => unitaryGaugeOrbit_trans h₁ h₂⟩

/-- Gauge equivalence: `Θ ≈ Ψ` iff one is the unitary conjugate of the other. -/
abbrev GaugeEquiv (Θ Ψ : HCParams n) : Prop := unitaryGaugeSetoid.r Θ Ψ

/-- The quotient by the gauge equivalence: a "gauge orbit space". -/
abbrev GaugeQuotient (n : ℕ) [NeZero n] := Quotient (unitaryGaugeSetoid : Setoid (HCParams n))

/-- The objective descends to the gauge quotient. -/
theorem objective_descends_to_gaugeQuotient (f : BinOp n) :
    ∀ {Θ Ψ : HCParams n}, GaugeEquiv Θ Ψ → objective Θ f = objective Ψ f := by
  intro Θ Ψ h
  exact (objective_constant_on_orbit Θ Ψ f h).symm

/-! ## hcNormSq gauge invariance -/

/-- `hcNormSq` is invariant under unitary conjugation. -/
theorem hcNormSq_unitaryConjAction (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1) (Θ : HCParams n) :
    Tikhonov.hcNormSq (unitaryConjAction U Θ) = Tikhonov.hcNormSq Θ := by
  unfold Tikhonov.hcNormSq
  congr 1
  · congr 1
    · apply Finset.sum_congr rfl
      intro a _
      show frobNormSq (U * Θ.A a * U.conjTranspose) = frobNormSq (Θ.A a)
      exact frobNormSq_unitaryConj U (Θ.A a) hU
    · apply Finset.sum_congr rfl
      intro b _
      show frobNormSq (U * Θ.B b * U.conjTranspose) = frobNormSq (Θ.B b)
      exact frobNormSq_unitaryConj U (Θ.B b) hU
  · apply Finset.sum_congr rfl
    intro c _
    show frobNormSq (U * Θ.C c * U.conjTranspose) = frobNormSq (Θ.C c)
    exact frobNormSq_unitaryConj U (Θ.C c) hU

/-- `hcNormSq` is constant on the unitary gauge orbit. -/
theorem hcNormSq_constant_on_orbit (Θ Ψ : HCParams n)
    (h : Ψ ∈ unitaryGaugeOrbit Θ) :
    Tikhonov.hcNormSq Ψ = Tikhonov.hcNormSq Θ := by
  obtain ⟨U, hU, hΨ⟩ := h
  rw [hΨ]
  exact hcNormSq_unitaryConjAction U hU Θ

/-! ## hcNormSq under uniformScale -/

/-- `hcNormSq` scales by `|t|²` under uniform scaling by `t`. -/
theorem hcNormSq_uniformScale (t : ℂ) (Θ : HCParams n) :
    Tikhonov.hcNormSq (uniformScale t Θ) =
    (t * starRingEnd ℂ t) * Tikhonov.hcNormSq Θ := by
  unfold Tikhonov.hcNormSq uniformScale
  simp only [frobNormSq_gaugeAction_A, frobNormSq_gaugeAction_B, frobNormSq_gaugeAction_C]
  rw [show (fun a => t * starRingEnd ℂ t * frobNormSq (Θ.A a)) =
          (fun a => (t * starRingEnd ℂ t) * frobNormSq (Θ.A a)) from rfl]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- For real `t`, `hcNormSq` scales by `t²` under uniform scaling. -/
theorem hcNormSq_re_uniformScale_real (t : ℝ) (Θ : HCParams n) :
    (Tikhonov.hcNormSq (uniformScale (t : ℂ) Θ)).re =
    t ^ 2 * (Tikhonov.hcNormSq Θ).re := by
  rw [hcNormSq_uniformScale]
  have h_star : starRingEnd ℂ ((t : ℂ)) = (t : ℂ) := Complex.conj_ofReal t
  rw [h_star]
  rw [show (t : ℂ) * (t : ℂ) = ((t ^ 2 : ℝ) : ℂ) from by push_cast; ring]
  rw [Complex.mul_re]
  show t ^ 2 * (Tikhonov.hcNormSq Θ).re - 0 * (Tikhonov.hcNormSq Θ).im =
      t ^ 2 * (Tikhonov.hcNormSq Θ).re
  ring

/-! ## inverseScalePenalty + misalignmentPenalty under unitary gauge -/

/-- `inverseScalePenalty` is invariant under unitary conjugation. -/
theorem inverseScalePenalty_unitaryConjAction (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1) (Θ : HCParams n) (f : BinOp n) :
    inverseScalePenalty (unitaryConjAction U Θ) f = inverseScalePenalty Θ f := by
  unfold inverseScalePenalty
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  set c := f.op a b
  have hT : hcProduct (unitaryConjAction U Θ) a b c = hcProduct Θ a b c :=
    hcProduct_unitaryConjAction U hU Θ a b c
  have hA : frobNormSq ((unitaryConjAction U Θ).A a) = frobNormSq (Θ.A a) := by
    show frobNormSq (U * Θ.A a * U.conjTranspose) = _
    exact frobNormSq_unitaryConj U (Θ.A a) hU
  have hB : frobNormSq ((unitaryConjAction U Θ).B b) = frobNormSq (Θ.B b) := by
    show frobNormSq (U * Θ.B b * U.conjTranspose) = _
    exact frobNormSq_unitaryConj U (Θ.B b) hU
  have hC : frobNormSq ((unitaryConjAction U Θ).C c) = frobNormSq (Θ.C c) := by
    show frobNormSq (U * Θ.C c * U.conjTranspose) = _
    exact frobNormSq_unitaryConj U (Θ.C c) hU
  show hcProduct (unitaryConjAction U Θ) a b c *
      starRingEnd ℂ (hcProduct (unitaryConjAction U Θ) a b c) *
      (1 / frobNormSq ((unitaryConjAction U Θ).A a) +
       1 / frobNormSq ((unitaryConjAction U Θ).B b) +
       1 / frobNormSq ((unitaryConjAction U Θ).C c)) = _
  rw [hT, hA, hB, hC]

/-- `misalignmentPenalty` is invariant under unitary conjugation, by the
    decomposition `objective = inverseScalePenalty + misalignmentPenalty`. -/
theorem misalignmentPenalty_unitaryConjAction (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1) (Θ : HCParams n) (f : BinOp n)
    (hnd : Nondegenerate Θ) (hnd' : Nondegenerate (unitaryConjAction U Θ)) :
    misalignmentPenalty (unitaryConjAction U Θ) f = misalignmentPenalty Θ f := by
  have h_obj : objective (unitaryConjAction U Θ) f = objective Θ f :=
    objective_unitaryConjAction U hU Θ f
  have h_ip : inverseScalePenalty (unitaryConjAction U Θ) f = inverseScalePenalty Θ f :=
    inverseScalePenalty_unitaryConjAction U hU Θ f
  have h_dec : objective Θ f = inverseScalePenalty Θ f + misalignmentPenalty Θ f :=
    decomposition Θ f hnd
  have h_dec' : objective (unitaryConjAction U Θ) f =
      inverseScalePenalty (unitaryConjAction U Θ) f +
      misalignmentPenalty (unitaryConjAction U Θ) f :=
    decomposition (unitaryConjAction U Θ) f hnd'
  -- Combining: ip + misalign' = obj' = obj = ip + misalign, hence misalign' = misalign.
  have key : inverseScalePenalty Θ f + misalignmentPenalty (unitaryConjAction U Θ) f =
      inverseScalePenalty Θ f + misalignmentPenalty Θ f := by
    calc inverseScalePenalty Θ f + misalignmentPenalty (unitaryConjAction U Θ) f
        = inverseScalePenalty (unitaryConjAction U Θ) f + misalignmentPenalty (unitaryConjAction U Θ) f := by
          rw [h_ip]
      _ = objective (unitaryConjAction U Θ) f := h_dec'.symm
      _ = objective Θ f := h_obj
      _ = inverseScalePenalty Θ f + misalignmentPenalty Θ f := h_dec
  exact add_left_cancel key

/-! ## uniformScale invertibility -/

/-- `uniformScale t` and `uniformScale t⁻¹` are inverse, for `t ≠ 0`. -/
theorem uniformScale_inv (t : ℂ) (ht : t ≠ 0) (Θ : HCParams n) :
    uniformScale t⁻¹ (uniformScale t Θ) = Θ := by
  rw [← uniformScale_mul]
  rw [show t⁻¹ * t = 1 from inv_mul_cancel₀ ht]
  exact uniformScale_one Θ

/-- `uniformScale t⁻¹` followed by `uniformScale t` is the identity. -/
theorem uniformScale_inv' (t : ℂ) (ht : t ≠ 0) (Θ : HCParams n) :
    uniformScale t (uniformScale t⁻¹ Θ) = Θ := by
  rw [← uniformScale_mul]
  rw [show t * t⁻¹ = 1 from mul_inv_cancel₀ ht]
  exact uniformScale_one Θ

/-! ## Gauge preserves UnitaryCollinear -/

/-- Unitary conjugation preserves `Nondegenerate`. -/
theorem nondegenerate_unitaryConjAction (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1) (Θ : HCParams n) (hnd : Nondegenerate Θ) :
    Nondegenerate (unitaryConjAction U Θ) := {
  A_pos := fun a => by
    show frobNormSq (U * Θ.A a * U.conjTranspose) ≠ 0
    rw [frobNormSq_unitaryConj U _ hU]
    exact hnd.A_pos a,
  B_pos := fun b => by
    show frobNormSq (U * Θ.B b * U.conjTranspose) ≠ 0
    rw [frobNormSq_unitaryConj U _ hU]
    exact hnd.B_pos b,
  C_pos := fun c => by
    show frobNormSq (U * Θ.C c * U.conjTranspose) ≠ 0
    rw [frobNormSq_unitaryConj U _ hU]
    exact hnd.C_pos c }

/-- Unitary conjugation preserves `M · Mᴴ = 1` (the unitarity property). -/
theorem unitarity_preserved_under_unitaryConj (U M : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1) (hM : M * M.conjTranspose = 1) :
    (U * M * U.conjTranspose) * (U * M * U.conjTranspose).conjTranspose = 1 := by
  -- (UMUᴴ)(UMUᴴ)ᴴ = UMUᴴ · UMᴴUᴴ = U·M·(Uᴴ·U)·Mᴴ·Uᴴ = U·(M·Mᴴ)·Uᴴ = U·1·Uᴴ = 1.
  have hU' : U.conjTranspose * U = 1 := mul_eq_one_comm.mp hU
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  -- Use simp + assoc to align everything.
  -- (UMUᴴ) * (UMᴴUᴴ) = UM (UᴴU) MᴴUᴴ = UMMᴴUᴴ = U (MMᴴ) Uᴴ = U Uᴴ = 1.
  have hU' : U.conjTranspose * U = 1 := mul_eq_one_comm.mp hU
  calc U * M * U.conjTranspose * (U * (M.conjTranspose * U.conjTranspose))
      = U * M * (U.conjTranspose * U) * M.conjTranspose * U.conjTranspose := by
        simp only [Matrix.mul_assoc]
    _ = U * M * 1 * M.conjTranspose * U.conjTranspose := by rw [hU']
    _ = U * (M * M.conjTranspose) * U.conjTranspose := by
        rw [Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = U * 1 * U.conjTranspose := by rw [hM]
    _ = 1 := by rw [Matrix.mul_one]; exact hU

/-- Unitary conjugation preserves `UnitaryCollinear`. -/
theorem unitaryCollinear_unitaryConjAction (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1) (Θ : HCParams n) (f : BinOp n)
    (huc : UnitaryCollinear Θ f) :
    UnitaryCollinear (unitaryConjAction U Θ) f := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- collinear: misalignmentPenalty = 0.
    have hnd_Θ : Nondegenerate Θ := {
      A_pos := fun a => by rw [frobNormSq_unitary_eq_one _ (huc.unitaryA a)]; exact one_ne_zero,
      B_pos := fun b => by rw [frobNormSq_unitary_eq_one _ (huc.unitaryB b)]; exact one_ne_zero,
      C_pos := fun c => by rw [frobNormSq_unitary_eq_one _ (huc.unitaryC c)]; exact one_ne_zero }
    have hnd' : Nondegenerate (unitaryConjAction U Θ) :=
      nondegenerate_unitaryConjAction U hU Θ hnd_Θ
    have h_misalign : misalignmentPenalty (unitaryConjAction U Θ) f =
        misalignmentPenalty Θ f :=
      misalignmentPenalty_unitaryConjAction U hU Θ f hnd_Θ hnd'
    show misalignmentPenalty (unitaryConjAction U Θ) f = 0
    rw [h_misalign]
    exact huc.collinear
  · -- feasible: Factorizes preserved.
    exact factorizes_unitaryConjAction Θ f huc.feasible U hU
  · -- unitaryA.
    intro a
    show (U * Θ.A a * U.conjTranspose) *
        (U * Θ.A a * U.conjTranspose).conjTranspose = 1
    exact unitarity_preserved_under_unitaryConj U (Θ.A a) hU (huc.unitaryA a)
  · intro b
    show (U * Θ.B b * U.conjTranspose) *
        (U * Θ.B b * U.conjTranspose).conjTranspose = 1
    exact unitarity_preserved_under_unitaryConj U (Θ.B b) hU (huc.unitaryB b)
  · intro c
    show (U * Θ.C c * U.conjTranspose) *
        (U * Θ.C c * U.conjTranspose).conjTranspose = 1
    exact unitarity_preserved_under_unitaryConj U (Θ.C c) hU (huc.unitaryC c)

/-! ## Inversion properties of unitary conjugation -/

/-- `unitaryConjAction Uᴴ` is the inverse of `unitaryConjAction U` for unitary `U`. -/
theorem unitaryConjAction_inv (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1) (Θ : HCParams n) :
    unitaryConjAction U.conjTranspose (unitaryConjAction U Θ) = Θ := by
  rw [unitaryConjAction_mul]
  -- Uᴴ * U = 1.
  have hU' : U.conjTranspose * U = 1 := mul_eq_one_comm.mp hU
  rw [hU']
  exact unitaryConjAction_one Θ

/-- `unitaryConjAction U` is the inverse of `unitaryConjAction Uᴴ`. -/
theorem unitaryConjAction_inv' (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1) (Θ : HCParams n) :
    unitaryConjAction U (unitaryConjAction U.conjTranspose Θ) = Θ := by
  rw [unitaryConjAction_mul]
  rw [hU]
  exact unitaryConjAction_one Θ

/-- The unitary conjugation map is bijective for any unitary `U`. -/
theorem unitaryConjAction_bijective (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1) :
    Function.Bijective (unitaryConjAction U : HCParams n → HCParams n) := by
  refine ⟨?_, ?_⟩
  · -- Injectivity: if U·Θ·Uᴴ = U·Ψ·Uᴴ as triples, then Θ = Ψ
    -- (apply unitaryConjAction Uᴴ to both sides).
    intro Θ Ψ h
    have := congrArg (unitaryConjAction U.conjTranspose) h
    rw [unitaryConjAction_inv U hU Θ] at this
    rw [unitaryConjAction_inv U hU Ψ] at this
    exact this
  · -- Surjectivity: any Ψ is the conjugation of (Uᴴ·Ψ·U).
    intro Ψ
    refine ⟨unitaryConjAction U.conjTranspose Ψ, ?_⟩
    exact unitaryConjAction_inv' U hU Ψ

/-! ## PerfectCollinearity gauge invariance -/

/-- `PerfectCollinearity` is preserved under unitary conjugation. -/
theorem perfectCollinearity_unitaryConjAction (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1) (Θ : HCParams n) (f : BinOp n)
    (hcol : PerfectCollinearity Θ f) (hnd : Nondegenerate Θ) :
    PerfectCollinearity (unitaryConjAction U Θ) f := by
  -- PerfectCollinearity ↔ misalignmentPenalty = 0.
  have hnd' : Nondegenerate (unitaryConjAction U Θ) :=
    nondegenerate_unitaryConjAction U hU Θ hnd
  have h_misalign : misalignmentPenalty (unitaryConjAction U Θ) f = misalignmentPenalty Θ f :=
    misalignmentPenalty_unitaryConjAction U hU Θ f hnd hnd'
  show misalignmentPenalty (unitaryConjAction U Θ) f = 0
  rw [h_misalign]
  exact hcol

/-- The "PerfectCollinearity + Factorizes + Nondegenerate" trifecta is preserved
    under unitary conjugation. -/
theorem PCFN_unitaryConjAction (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1) (Θ : HCParams n) (f : BinOp n)
    (hcol : PerfectCollinearity Θ f) (hfeas : Factorizes Θ f)
    (hnd : Nondegenerate Θ) :
    PerfectCollinearity (unitaryConjAction U Θ) f ∧
    Factorizes (unitaryConjAction U Θ) f ∧
    Nondegenerate (unitaryConjAction U Θ) :=
  ⟨perfectCollinearity_unitaryConjAction U hU Θ f hcol hnd,
   factorizes_unitaryConjAction Θ f hfeas U hU,
   nondegenerate_unitaryConjAction U hU Θ hnd⟩

/-! ## κ=1 hypothesis gauge invariance -/

/-- The "κ=1 on support" hypothesis is preserved under unitary conjugation. -/
theorem kappa_one_unitaryConjAction (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1) (Θ : HCParams n) (f : BinOp n)
    (hκ : ∀ a b : Fin n, kappaTriple Θ a b (f.op a b) = 1) :
    ∀ a b : Fin n, kappaTriple (unitaryConjAction U Θ) a b (f.op a b) = 1 := by
  intro a b
  rw [kappaTriple_unitaryConjAction U hU]
  exact hκ a b

/-- The discharge hypotheses for `kappa_one_collinear_to_unitary_collinear`
    (PerfectCollinearity + Nondegenerate + Factorizes + κ=1) are all preserved
    under unitary conjugation. -/
theorem kappa_one_PCFN_unitaryConjAction (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1) (Θ : HCParams n) (f : BinOp n)
    (hcol : PerfectCollinearity Θ f) (hfeas : Factorizes Θ f)
    (hnd : Nondegenerate Θ)
    (hκ : ∀ a b : Fin n, kappaTriple Θ a b (f.op a b) = 1) :
    PerfectCollinearity (unitaryConjAction U Θ) f ∧
    Factorizes (unitaryConjAction U Θ) f ∧
    Nondegenerate (unitaryConjAction U Θ) ∧
    (∀ a b : Fin n, kappaTriple (unitaryConjAction U Θ) a b (f.op a b) = 1) := by
  obtain ⟨hcol', hfeas', hnd'⟩ := PCFN_unitaryConjAction U hU Θ f hcol hfeas hnd
  exact ⟨hcol', hfeas', hnd', kappa_one_unitaryConjAction U hU Θ f hκ⟩

/-! ## Cube roots of unity as a discrete gauge -/

/-- For `t³ = 1` (cube root of unity), `t` has unit modulus: `t · star t = 1`. -/
theorem cubeRoot_norm_one (t : ℂ) (ht : t ^ 3 = 1) :
    t * starRingEnd ℂ t = 1 := by
  -- t^3 = 1 ⟹ |t|^6 = |t^3|² = 1 ⟹ |t|² = 1 (since |t|² ≥ 0).
  have hnorm : Complex.normSq t * Complex.normSq t * Complex.normSq t = 1 := by
    have := congrArg Complex.normSq ht
    rw [show Complex.normSq (t ^ 3) = Complex.normSq t * Complex.normSq t * Complex.normSq t
        from by rw [show t ^ 3 = t * t * t from by ring]; rw [map_mul, map_mul]] at this
    rwa [Complex.normSq_one] at this
  have hnorm_nn : 0 ≤ Complex.normSq t := Complex.normSq_nonneg _
  -- |t|² ^ 3 = 1 ⟹ |t|² = 1 (real cube root of 1).
  have hnorm_one : Complex.normSq t = 1 := by
    have : (Complex.normSq t) ^ 3 = 1 := by
      rw [show (Complex.normSq t) ^ 3 =
          Complex.normSq t * Complex.normSq t * Complex.normSq t from by ring]
      exact hnorm
    -- For nonneg reals: x^3 = 1 ⟹ x = 1.
    nlinarith [sq_nonneg (Complex.normSq t - 1),
               sq_nonneg (Complex.normSq t + 1),
               hnorm_nn]
  rw [Complex.mul_conj, hnorm_one, Complex.ofReal_one]

/-- For `t³ = 1`, `uniformScale t` preserves `Factorizes`. -/
theorem factorizes_uniformScale_cubeRoot (t : ℂ) (ht : t ^ 3 = 1)
    (Θ : HCParams n) (f : BinOp n) (hfeas : Factorizes Θ f) :
    Factorizes (uniformScale t Θ) f := by
  intro a b c
  rw [hcProduct_uniformScale]
  by_cases hc : c = f.op a b
  · subst hc
    have hT : hcProduct Θ a b (f.op a b) = 1 := by
      have := hfeas a b (f.op a b)
      rwa [structureTensor, if_pos rfl] at this
    rw [hT, mul_one, ht, structureTensor, if_pos rfl]
  · have hT : hcProduct Θ a b c = 0 := by
      have := hfeas a b c
      rwa [structureTensor, if_neg (Ne.symm hc)] at this
    rw [hT, mul_zero, structureTensor, if_neg (Ne.symm hc)]

/-- For `t³ = 1` (cube root of unity), `uniformScale t` preserves the
    objective `H` (since `|t|⁴ = 1`). -/
theorem objective_uniformScale_cubeRoot (t : ℂ) (ht : t ^ 3 = 1)
    (Θ : HCParams n) (f : BinOp n) :
    objective (uniformScale t Θ) f = objective Θ f := by
  rw [objective_uniformScale]
  rw [show (t * starRingEnd ℂ t) ^ 2 = (t * starRingEnd ℂ t) * (t * starRingEnd ℂ t) from by ring]
  rw [cubeRoot_norm_one t ht, one_mul, one_mul]

/-! ## gaugeAction composition + inversion -/

/-- `gaugeAction` composes via per-slot multiplication. -/
theorem gaugeAction_mul (sA₁ sB₁ sC₁ sA₂ sB₂ sC₂ : Fin n → ℂ) (Θ : HCParams n) :
    gaugeAction sA₂ sB₂ sC₂ (gaugeAction sA₁ sB₁ sC₁ Θ) =
    gaugeAction (fun a => sA₂ a * sA₁ a) (fun b => sB₂ b * sB₁ b) (fun c => sC₂ c * sC₁ c) Θ := by
  unfold gaugeAction
  cases Θ
  simp only [HCParams.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  all_goals
    funext _
    rw [smul_smul]

/-- For nonzero per-slot factors, `gaugeAction` is invertible via the
    componentwise inverses. -/
theorem gaugeAction_inv (sA sB sC : Fin n → ℂ)
    (hA : ∀ a, sA a ≠ 0) (hB : ∀ b, sB b ≠ 0) (hC : ∀ c, sC c ≠ 0)
    (Θ : HCParams n) :
    gaugeAction (fun a => (sA a)⁻¹) (fun b => (sB b)⁻¹) (fun c => (sC c)⁻¹)
      (gaugeAction sA sB sC Θ) = Θ := by
  rw [gaugeAction_mul]
  unfold gaugeAction
  cases Θ
  simp only [HCParams.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext a
    rw [show (sA a)⁻¹ * sA a = 1 from inv_mul_cancel₀ (hA a), one_smul]
  · funext b
    rw [show (sB b)⁻¹ * sB b = 1 from inv_mul_cancel₀ (hB b), one_smul]
  · funext c
    rw [show (sC c)⁻¹ * sC c = 1 from inv_mul_cancel₀ (hC c), one_smul]

/-- `gaugeAction` is bijective when all per-slot factors are nonzero. -/
theorem gaugeAction_bijective (sA sB sC : Fin n → ℂ)
    (hA : ∀ a, sA a ≠ 0) (hB : ∀ b, sB b ≠ 0) (hC : ∀ c, sC c ≠ 0) :
    Function.Bijective (gaugeAction sA sB sC : HCParams n → HCParams n) := by
  refine ⟨?_, ?_⟩
  · -- Injectivity: if gauge actions of Θ and Ψ agree, then Θ = Ψ.
    intro Θ Ψ h
    have := congrArg
      (gaugeAction (fun a => (sA a)⁻¹) (fun b => (sB b)⁻¹) (fun c => (sC c)⁻¹)) h
    rw [gaugeAction_inv sA sB sC hA hB hC Θ] at this
    rw [gaugeAction_inv sA sB sC hA hB hC Ψ] at this
    exact this
  · -- Surjectivity: any Ψ is the gauge of `gaugeAction (s⁻¹) Ψ`.
    intro Ψ
    refine ⟨gaugeAction (fun a => (sA a)⁻¹) (fun b => (sB b)⁻¹) (fun c => (sC c)⁻¹) Ψ, ?_⟩
    rw [gaugeAction_mul]
    unfold gaugeAction
    cases Ψ
    simp only [HCParams.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · funext a
      rw [show sA a * (sA a)⁻¹ = 1 from mul_inv_cancel₀ (hA a), one_smul]
    · funext b
      rw [show sB b * (sB b)⁻¹ = 1 from mul_inv_cancel₀ (hB b), one_smul]
    · funext c
      rw [show sC c * (sC c)⁻¹ = 1 from mul_inv_cancel₀ (hC c), one_smul]

/-! ## gaugeAction preserves Nondegenerate -/

/-- For complex `z`, `z * conj(z) ≠ 0` iff `z ≠ 0`. -/
private lemma mul_conj_ne_zero {z : ℂ} (hz : z ≠ 0) : z * starRingEnd ℂ z ≠ 0 := by
  rw [Complex.mul_conj]
  exact_mod_cast (mt Complex.normSq_eq_zero.mp) hz

/-- `gaugeAction` preserves `Nondegenerate` whenever all per-slot factors are nonzero. -/
theorem nondegenerate_gaugeAction (sA sB sC : Fin n → ℂ)
    (hA : ∀ a, sA a ≠ 0) (hB : ∀ b, sB b ≠ 0) (hC : ∀ c, sC c ≠ 0)
    {Θ : HCParams n} (hΘ : Nondegenerate Θ) :
    Nondegenerate (gaugeAction sA sB sC Θ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    rw [frobNormSq_gaugeAction_A]
    exact mul_ne_zero (mul_conj_ne_zero (hA a)) (hΘ.A_pos a)
  · intro b
    rw [frobNormSq_gaugeAction_B]
    exact mul_ne_zero (mul_conj_ne_zero (hB b)) (hΘ.B_pos b)
  · intro c
    rw [frobNormSq_gaugeAction_C]
    exact mul_ne_zero (mul_conj_ne_zero (hC c)) (hΘ.C_pos c)

/-- Conversely: if `gaugeAction` of `Θ` is `Nondegenerate` (with nonzero factors), so is `Θ`. -/
theorem nondegenerate_of_gaugeAction (sA sB sC : Fin n → ℂ)
    (hA : ∀ a, sA a ≠ 0) (hB : ∀ b, sB b ≠ 0) (hC : ∀ c, sC c ≠ 0)
    {Θ : HCParams n} (hg : Nondegenerate (gaugeAction sA sB sC Θ)) :
    Nondegenerate Θ := by
  have heq : Θ = gaugeAction (fun a => (sA a)⁻¹) (fun b => (sB b)⁻¹) (fun c => (sC c)⁻¹)
      (gaugeAction sA sB sC Θ) := (gaugeAction_inv sA sB sC hA hB hC Θ).symm
  rw [heq]
  exact nondegenerate_gaugeAction _ _ _
    (fun a => inv_ne_zero (hA a)) (fun b => inv_ne_zero (hB b)) (fun c => inv_ne_zero (hC c)) hg

/-- Two-sided: nondegeneracy is invariant under nonzero gauge action. -/
theorem nondegenerate_gaugeAction_iff (sA sB sC : Fin n → ℂ)
    (hA : ∀ a, sA a ≠ 0) (hB : ∀ b, sB b ≠ 0) (hC : ∀ c, sC c ≠ 0) (Θ : HCParams n) :
    Nondegenerate (gaugeAction sA sB sC Θ) ↔ Nondegenerate Θ :=
  ⟨nondegenerate_of_gaugeAction sA sB sC hA hB hC,
   nondegenerate_gaugeAction sA sB sC hA hB hC⟩

/-! ## gaugeAction and unitaryConjAction commute -/

/-- Per-slot scaling commutes with unitary conjugation: scaling pulls through
    `U * (sA a • A_a) * Uᴴ = sA a • (U * A_a * Uᴴ)`. -/
theorem gaugeAction_unitaryConjAction_comm (sA sB sC : Fin n → ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ) (Θ : HCParams n) :
    unitaryConjAction U (gaugeAction sA sB sC Θ) =
    gaugeAction sA sB sC (unitaryConjAction U Θ) := by
  unfold unitaryConjAction gaugeAction
  cases Θ
  simp only [HCParams.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  all_goals
    funext _
    simp only [Matrix.mul_smul, Matrix.smul_mul]

/-- Composite gauge invariance: for any cube root of unity `t` and unitary `U`, the
    composite `unitaryConjAction U ∘ uniformScale t` preserves the objective. -/
theorem objective_uniformScale_unitaryConj_cubeRoot (t : ℂ) (ht : t ^ 3 = 1)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U * U.conjTranspose = 1)
    (Θ : HCParams n) (f : BinOp n) :
    objective (unitaryConjAction U (uniformScale t Θ)) f = objective Θ f := by
  rw [objective_unitaryConjAction U hU, objective_uniformScale_cubeRoot t ht]

/-- And in the other order: `uniformScale t ∘ unitaryConjAction U` also preserves the
    objective when `t³ = 1` and `U` is unitary. -/
theorem objective_unitaryConj_uniformScale_cubeRoot (t : ℂ) (ht : t ^ 3 = 1)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U * U.conjTranspose = 1)
    (Θ : HCParams n) (f : BinOp n) :
    objective (uniformScale t (unitaryConjAction U Θ)) f = objective Θ f := by
  rw [objective_uniformScale_cubeRoot t ht, objective_unitaryConjAction U hU]

/-- Combined gauge invariance for `Factorizes`: if the per-slot factors satisfy the
    support cocycle condition `s_A a · s_B b · s_C (f.op a b) = 1` and `U` is unitary,
    then both gauge actions composed preserve feasibility. -/
theorem factorizes_unitaryConj_gaugeAction (sA sB sC : Fin n → ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U * U.conjTranspose = 1)
    (Θ : HCParams n) (f : BinOp n) (hfeas : Factorizes Θ f)
    (h_unit : ∀ a b : Fin n, sA a * sB b * sC (f.op a b) = 1) :
    Factorizes (unitaryConjAction U (gaugeAction sA sB sC Θ)) f := by
  apply factorizes_unitaryConjAction _ _ _ U hU
  exact (factorizes_gaugeAction_iff sA sB sC Θ f hfeas).mpr h_unit

/-- Same combined invariance in the swapped order. Uses commutativity of the two actions. -/
theorem factorizes_gaugeAction_unitaryConj (sA sB sC : Fin n → ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U * U.conjTranspose = 1)
    (Θ : HCParams n) (f : BinOp n) (hfeas : Factorizes Θ f)
    (h_unit : ∀ a b : Fin n, sA a * sB b * sC (f.op a b) = 1) :
    Factorizes (gaugeAction sA sB sC (unitaryConjAction U Θ)) f := by
  rw [← gaugeAction_unitaryConjAction_comm]
  exact factorizes_unitaryConj_gaugeAction sA sB sC U hU Θ f hfeas h_unit

/-! ## hcNormSq under gaugeAction + combined orbit -/

/-- `hcNormSq` under `gaugeAction`: each slice contributes `|s_x|²` weighting. -/
theorem hcNormSq_gaugeAction (sA sB sC : Fin n → ℂ) (Θ : HCParams n) :
    Tikhonov.hcNormSq (gaugeAction sA sB sC Θ) =
      ∑ a : Fin n, (sA a * starRingEnd ℂ (sA a)) * frobNormSq (Θ.A a) +
      ∑ b : Fin n, (sB b * starRingEnd ℂ (sB b)) * frobNormSq (Θ.B b) +
      ∑ c : Fin n, (sC c * starRingEnd ℂ (sC c)) * frobNormSq (Θ.C c) := by
  unfold Tikhonov.hcNormSq
  congr 1
  · congr 1
    · apply Finset.sum_congr rfl
      intro a _
      exact frobNormSq_gaugeAction_A sA sB sC Θ a
    · apply Finset.sum_congr rfl
      intro b _
      exact frobNormSq_gaugeAction_B sA sB sC Θ b
  · apply Finset.sum_congr rfl
    intro c _
    exact frobNormSq_gaugeAction_C sA sB sC Θ c

/-- When all per-slot factors are equal to `t`, `hcNormSq_gaugeAction` reduces to the
    `uniformScale` formula. -/
theorem hcNormSq_gaugeAction_uniform (t : ℂ) (Θ : HCParams n) :
    Tikhonov.hcNormSq (gaugeAction (fun _ => t) (fun _ => t) (fun _ => t) Θ) =
    (t * starRingEnd ℂ t) * Tikhonov.hcNormSq Θ := by
  show Tikhonov.hcNormSq (uniformScale t Θ) = _
  exact hcNormSq_uniformScale t Θ

/-- Combined: applying `unitaryConjAction U` after `gaugeAction sA sB sC` gives the
    same `hcNormSq` formula as `gaugeAction` alone (unitary conjugation preserves
    Frobenius norms). -/
theorem hcNormSq_unitaryConj_gaugeAction (sA sB sC : Fin n → ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U * U.conjTranspose = 1) (Θ : HCParams n) :
    Tikhonov.hcNormSq (unitaryConjAction U (gaugeAction sA sB sC Θ)) =
      ∑ a : Fin n, (sA a * starRingEnd ℂ (sA a)) * frobNormSq (Θ.A a) +
      ∑ b : Fin n, (sB b * starRingEnd ℂ (sB b)) * frobNormSq (Θ.B b) +
      ∑ c : Fin n, (sC c * starRingEnd ℂ (sC c)) * frobNormSq (Θ.C c) := by
  rw [hcNormSq_unitaryConjAction U hU, hcNormSq_gaugeAction]

/-- And the reverse composition: `gaugeAction` after `unitaryConjAction` is the same
    formula. (Follows from `hcNormSq_unitaryConj_gaugeAction` via the commutativity
    of the two actions.) -/
theorem hcNormSq_gaugeAction_unitaryConj (sA sB sC : Fin n → ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U * U.conjTranspose = 1) (Θ : HCParams n) :
    Tikhonov.hcNormSq (gaugeAction sA sB sC (unitaryConjAction U Θ)) =
      ∑ a : Fin n, (sA a * starRingEnd ℂ (sA a)) * frobNormSq (Θ.A a) +
      ∑ b : Fin n, (sB b * starRingEnd ℂ (sB b)) * frobNormSq (Θ.B b) +
      ∑ c : Fin n, (sC c * starRingEnd ℂ (sC c)) * frobNormSq (Θ.C c) := by
  rw [← gaugeAction_unitaryConjAction_comm]
  exact hcNormSq_unitaryConj_gaugeAction sA sB sC U hU Θ

/-- For any cube root of unity `t`, the combined `unitaryConjAction U ∘ uniformScale t`
    leaves `hcNormSq` invariant: cube roots of unity have `t · conj(t) = 1`. -/
theorem hcNormSq_unitaryConj_uniformScale_cubeRoot (t : ℂ) (ht : t ^ 3 = 1)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U * U.conjTranspose = 1) (Θ : HCParams n) :
    Tikhonov.hcNormSq (unitaryConjAction U (uniformScale t Θ)) = Tikhonov.hcNormSq Θ := by
  rw [hcNormSq_unitaryConjAction U hU, hcNormSq_uniformScale, cubeRoot_norm_one t ht, one_mul]

/-- And in the reverse compose order, by commutativity. -/
theorem hcNormSq_uniformScale_unitaryConj_cubeRoot (t : ℂ) (ht : t ^ 3 = 1)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U * U.conjTranspose = 1) (Θ : HCParams n) :
    Tikhonov.hcNormSq (uniformScale t (unitaryConjAction U Θ)) = Tikhonov.hcNormSq Θ := by
  rw [hcNormSq_uniformScale, hcNormSq_unitaryConjAction U hU, cubeRoot_norm_one t ht, one_mul]

/-! ## kappaTriple invariance under gaugeAction (nonzero factors) -/

/-- `kappaTriple` is invariant under per-slot scaling by nonzero factors. The numerator
    `‖A‖²‖B‖²‖C‖²` and the denominator `T · conj T` both pick up the same factor
    `|sA|²|sB|²|sC|²`, which cancels. -/
theorem kappaTriple_gaugeAction (sA sB sC : Fin n → ℂ)
    (hA : ∀ a, sA a ≠ 0) (hB : ∀ b, sB b ≠ 0) (hC : ∀ c, sC c ≠ 0)
    (Θ : HCParams n) (a b c : Fin n) :
    kappaTriple (gaugeAction sA sB sC Θ) a b c = kappaTriple Θ a b c := by
  unfold kappaTriple
  rw [frobNormSq_gaugeAction_A, frobNormSq_gaugeAction_B, frobNormSq_gaugeAction_C,
      hcProduct_gaugeAction]
  simp only [map_mul]
  -- Repackage numerator: factor out (|sA|²|sB|²|sC|²).
  rw [show
    sA a * starRingEnd ℂ (sA a) * frobNormSq (Θ.A a) *
    (sB b * starRingEnd ℂ (sB b) * frobNormSq (Θ.B b)) *
    (sC c * starRingEnd ℂ (sC c) * frobNormSq (Θ.C c)) =
    (sA a * starRingEnd ℂ (sA a) *
       (sB b * starRingEnd ℂ (sB b)) * (sC c * starRingEnd ℂ (sC c))) *
    (frobNormSq (Θ.A a) * frobNormSq (Θ.B b) * frobNormSq (Θ.C c)) from by ring]
  rw [show
    sA a * sB b * sC c * hcProduct Θ a b c *
    (starRingEnd ℂ (sA a) * starRingEnd ℂ (sB b) * starRingEnd ℂ (sC c) *
     starRingEnd ℂ (hcProduct Θ a b c)) =
    (sA a * starRingEnd ℂ (sA a) *
       (sB b * starRingEnd ℂ (sB b)) * (sC c * starRingEnd ℂ (sC c))) *
    (hcProduct Θ a b c * starRingEnd ℂ (hcProduct Θ a b c)) from by ring]
  exact mul_div_mul_left _ _
    (mul_ne_zero (mul_ne_zero (mul_conj_ne_zero (hA a)) (mul_conj_ne_zero (hB b)))
      (mul_conj_ne_zero (hC c)))

/-- Combined: `kappaTriple` is invariant under (unitaryConjAction U) ∘ (gaugeAction s),
    when `U` is unitary and the per-slot factors are nonzero. -/
theorem kappaTriple_unitaryConj_gaugeAction (sA sB sC : Fin n → ℂ)
    (hA : ∀ a, sA a ≠ 0) (hB : ∀ b, sB b ≠ 0) (hC : ∀ c, sC c ≠ 0)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U * U.conjTranspose = 1)
    (Θ : HCParams n) (a b c : Fin n) :
    kappaTriple (unitaryConjAction U (gaugeAction sA sB sC Θ)) a b c =
    kappaTriple Θ a b c := by
  rw [kappaTriple_unitaryConjAction U hU,
      kappaTriple_gaugeAction sA sB sC hA hB hC]

/-- Reverse compose order: invariance is preserved by commutativity of the actions. -/
theorem kappaTriple_gaugeAction_unitaryConj (sA sB sC : Fin n → ℂ)
    (hA : ∀ a, sA a ≠ 0) (hB : ∀ b, sB b ≠ 0) (hC : ∀ c, sC c ≠ 0)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U * U.conjTranspose = 1)
    (Θ : HCParams n) (a b c : Fin n) :
    kappaTriple (gaugeAction sA sB sC (unitaryConjAction U Θ)) a b c =
    kappaTriple Θ a b c := by
  rw [← gaugeAction_unitaryConjAction_comm]
  exact kappaTriple_unitaryConj_gaugeAction sA sB sC hA hB hC U hU Θ a b c

/-! ## inverseScalePenalty under uniformScale (cube-root invariance) -/

/-- `inverseScalePenalty` is invariant under `uniformScale` by a cube root of unity.
    Both `|hcProduct|²` and `1/‖slice‖²` are invariant when `t · conj t = 1`,
    because `t³ = 1` implies `|t| = 1`. -/
theorem inverseScalePenalty_uniformScale_cubeRoot (t : ℂ) (ht : t ^ 3 = 1)
    (Θ : HCParams n) (f : BinOp n) :
    inverseScalePenalty (uniformScale t Θ) f = inverseScalePenalty Θ f := by
  unfold inverseScalePenalty
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  set c := f.op a b
  have hT : hcProduct (uniformScale t Θ) a b c = t ^ 3 * hcProduct Θ a b c :=
    hcProduct_uniformScale t Θ a b c
  have hA : frobNormSq ((uniformScale t Θ).A a) =
      (t * starRingEnd ℂ t) * frobNormSq (Θ.A a) := frobNormSq_uniformScale_A t Θ a
  have hB : frobNormSq ((uniformScale t Θ).B b) =
      (t * starRingEnd ℂ t) * frobNormSq (Θ.B b) := by
    show frobNormSq (t • Θ.B b) = _
    rw [frobNormSq_smul]
  have hC : frobNormSq ((uniformScale t Θ).C c) =
      (t * starRingEnd ℂ t) * frobNormSq (Θ.C c) := by
    show frobNormSq (t • Θ.C c) = _
    rw [frobNormSq_smul]
  show hcProduct (uniformScale t Θ) a b c *
        starRingEnd ℂ (hcProduct (uniformScale t Θ) a b c) *
        (1 / frobNormSq ((uniformScale t Θ).A a) +
         1 / frobNormSq ((uniformScale t Θ).B b) +
         1 / frobNormSq ((uniformScale t Θ).C c)) = _
  rw [hT, hA, hB, hC]
  -- |t|² = 1 since t³ = 1
  have h_norm : t * starRingEnd ℂ t = 1 := cubeRoot_norm_one t ht
  -- |t³|² = (t·conj t)³ = 1³ = 1
  have h_norm3 : t ^ 3 * starRingEnd ℂ (t ^ 3) = 1 := by
    rw [ht, map_one, one_mul]
  rw [show t ^ 3 * hcProduct Θ a b c * starRingEnd ℂ (t ^ 3 * hcProduct Θ a b c) =
        (t ^ 3 * starRingEnd ℂ (t ^ 3)) *
        (hcProduct Θ a b c * starRingEnd ℂ (hcProduct Θ a b c)) from by
    rw [map_mul]; ring]
  rw [h_norm3, one_mul]
  congr 1
  rw [h_norm]
  simp only [one_mul]

/-- Combined: `inverseScalePenalty` is invariant under cube-root scaling AND unitary
    conjugation. -/
theorem inverseScalePenalty_unitaryConj_uniformScale_cubeRoot (t : ℂ) (ht : t ^ 3 = 1)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U * U.conjTranspose = 1)
    (Θ : HCParams n) (f : BinOp n) :
    inverseScalePenalty (unitaryConjAction U (uniformScale t Θ)) f = inverseScalePenalty Θ f := by
  rw [inverseScalePenalty_unitaryConjAction U hU,
      inverseScalePenalty_uniformScale_cubeRoot t ht]

/-- Reverse compose order. Note: this is a separate proof since we don't have a
    direct `uniformScale t (unitaryConjAction U Θ) = unitaryConjAction U (uniformScale t Θ)`
    rewrite available globally — we apply the cube-root invariance after unwinding
    the unitary action's preservation of the penalty. -/
theorem inverseScalePenalty_uniformScale_unitaryConj_cubeRoot (t : ℂ) (ht : t ^ 3 = 1)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U * U.conjTranspose = 1)
    (Θ : HCParams n) (f : BinOp n) :
    inverseScalePenalty (uniformScale t (unitaryConjAction U Θ)) f = inverseScalePenalty Θ f := by
  rw [inverseScalePenalty_uniformScale_cubeRoot t ht,
      inverseScalePenalty_unitaryConjAction U hU]

/-! ## misalignmentPenalty under uniformScale (cube-root invariance) -/

/-- Cube roots of unity are nonzero. -/
private lemma cubeRoot_ne_zero {t : ℂ} (ht : t ^ 3 = 1) : t ≠ 0 := by
  intro h
  rw [h, zero_pow (by norm_num : 3 ≠ 0)] at ht
  exact zero_ne_one ht

/-- `misalignmentPenalty` is invariant under `uniformScale` by a cube root of unity.
    Proof: combine `objective_uniformScale_cubeRoot` and
    `inverseScalePenalty_uniformScale_cubeRoot` via the decomposition
    `objective = inverseScalePenalty + misalignmentPenalty`. -/
theorem misalignmentPenalty_uniformScale_cubeRoot (t : ℂ) (ht : t ^ 3 = 1)
    (Θ : HCParams n) (f : BinOp n) (hnd : Nondegenerate Θ) :
    misalignmentPenalty (uniformScale t Θ) f = misalignmentPenalty Θ f := by
  -- uniformScale by a nonzero scalar preserves Nondegenerate.
  have ht_ne : t ≠ 0 := cubeRoot_ne_zero ht
  have hnd' : Nondegenerate (uniformScale t Θ) :=
    nondegenerate_gaugeAction _ _ _
      (fun _ => ht_ne) (fun _ => ht_ne) (fun _ => ht_ne) hnd
  have h_obj : objective (uniformScale t Θ) f = objective Θ f :=
    objective_uniformScale_cubeRoot t ht Θ f
  have h_ip : inverseScalePenalty (uniformScale t Θ) f = inverseScalePenalty Θ f :=
    inverseScalePenalty_uniformScale_cubeRoot t ht Θ f
  have h_dec : objective Θ f = inverseScalePenalty Θ f + misalignmentPenalty Θ f :=
    decomposition Θ f hnd
  have h_dec' : objective (uniformScale t Θ) f =
      inverseScalePenalty (uniformScale t Θ) f +
      misalignmentPenalty (uniformScale t Θ) f :=
    decomposition (uniformScale t Θ) f hnd'
  -- Combine: ip + misalign' = obj' = obj = ip + misalign, hence misalign' = misalign.
  have key : inverseScalePenalty Θ f + misalignmentPenalty (uniformScale t Θ) f =
      inverseScalePenalty Θ f + misalignmentPenalty Θ f := by
    calc inverseScalePenalty Θ f + misalignmentPenalty (uniformScale t Θ) f
        = inverseScalePenalty (uniformScale t Θ) f +
            misalignmentPenalty (uniformScale t Θ) f := by rw [h_ip]
      _ = objective (uniformScale t Θ) f := h_dec'.symm
      _ = objective Θ f := h_obj
      _ = inverseScalePenalty Θ f + misalignmentPenalty Θ f := h_dec
  exact add_left_cancel key

/-- Combined: `misalignmentPenalty` is invariant under cube-root scaling AND unitary
    conjugation. -/
theorem misalignmentPenalty_unitaryConj_uniformScale_cubeRoot (t : ℂ) (ht : t ^ 3 = 1)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U * U.conjTranspose = 1)
    (Θ : HCParams n) (f : BinOp n) (hnd : Nondegenerate Θ) :
    misalignmentPenalty (unitaryConjAction U (uniformScale t Θ)) f = misalignmentPenalty Θ f := by
  have ht_ne : t ≠ 0 := cubeRoot_ne_zero ht
  have hnd1 : Nondegenerate (uniformScale t Θ) :=
    nondegenerate_gaugeAction _ _ _
      (fun _ => ht_ne) (fun _ => ht_ne) (fun _ => ht_ne) hnd
  rw [misalignmentPenalty_unitaryConjAction U hU _ f hnd1
        (nondegenerate_unitaryConjAction U hU _ hnd1),
      misalignmentPenalty_uniformScale_cubeRoot t ht Θ f hnd]

/-! ## PerfectCollinearity / PCFN cube-root invariance -/

/-- `PerfectCollinearity` is preserved under `uniformScale` by a cube root of unity
    (PerfectCollinearity ↔ misalignmentPenalty = 0). -/
theorem perfectCollinearity_uniformScale_cubeRoot (t : ℂ) (ht : t ^ 3 = 1)
    (Θ : HCParams n) (f : BinOp n)
    (hcol : PerfectCollinearity Θ f) (hnd : Nondegenerate Θ) :
    PerfectCollinearity (uniformScale t Θ) f := by
  show misalignmentPenalty (uniformScale t Θ) f = 0
  rw [misalignmentPenalty_uniformScale_cubeRoot t ht Θ f hnd]
  exact hcol

/-- The "PerfectCollinearity + Factorizes + Nondegenerate" trifecta is preserved
    under cube-root uniform scaling. -/
theorem PCFN_uniformScale_cubeRoot (t : ℂ) (ht : t ^ 3 = 1)
    (Θ : HCParams n) (f : BinOp n)
    (hcol : PerfectCollinearity Θ f) (hfeas : Factorizes Θ f)
    (hnd : Nondegenerate Θ) :
    PerfectCollinearity (uniformScale t Θ) f ∧
    Factorizes (uniformScale t Θ) f ∧
    Nondegenerate (uniformScale t Θ) := by
  have ht_ne : t ≠ 0 := cubeRoot_ne_zero ht
  refine ⟨?_, ?_, ?_⟩
  · exact perfectCollinearity_uniformScale_cubeRoot t ht Θ f hcol hnd
  · exact factorizes_uniformScale_cubeRoot t ht Θ f hfeas
  · exact nondegenerate_gaugeAction _ _ _
      (fun _ => ht_ne) (fun _ => ht_ne) (fun _ => ht_ne) hnd

/-- Composite: PCFN preserved under unitary conjugation AND cube-root scaling. -/
theorem PCFN_unitaryConj_uniformScale_cubeRoot (t : ℂ) (ht : t ^ 3 = 1)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U * U.conjTranspose = 1)
    (Θ : HCParams n) (f : BinOp n)
    (hcol : PerfectCollinearity Θ f) (hfeas : Factorizes Θ f)
    (hnd : Nondegenerate Θ) :
    PerfectCollinearity (unitaryConjAction U (uniformScale t Θ)) f ∧
    Factorizes (unitaryConjAction U (uniformScale t Θ)) f ∧
    Nondegenerate (unitaryConjAction U (uniformScale t Θ)) := by
  obtain ⟨hcol1, hfeas1, hnd1⟩ := PCFN_uniformScale_cubeRoot t ht Θ f hcol hfeas hnd
  exact PCFN_unitaryConjAction U hU _ f hcol1 hfeas1 hnd1

/-! ## UnitaryCollinear cube-root invariance -/

/-- Unitarity is preserved under scaling by `t` with `|t|² = 1`:
    `(t • M) · (t • M)ᴴ = (t·conj t) · (M·Mᴴ) = 1 · 1 = 1`. -/
theorem unitarity_preserved_under_unit_scale (t : ℂ) (M : Matrix (Fin n) (Fin n) ℂ)
    (h_norm : t * starRingEnd ℂ t = 1) (hM : M * M.conjTranspose = 1) :
    (t • M) * (t • M).conjTranspose = 1 := by
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have h_star : t * star t = 1 := h_norm
  rw [h_star, one_smul, hM]

/-- `UnitaryCollinear` is preserved under `uniformScale` by a cube root of unity. -/
theorem unitaryCollinear_uniformScale_cubeRoot (t : ℂ) (ht : t ^ 3 = 1)
    (Θ : HCParams n) (f : BinOp n) (huc : UnitaryCollinear Θ f) :
    UnitaryCollinear (uniformScale t Θ) f := by
  have h_norm : t * starRingEnd ℂ t = 1 := cubeRoot_norm_one t ht
  -- Recover Nondegenerate from unitarity of slices.
  have hnd_Θ : Nondegenerate Θ := {
    A_pos := fun a => by rw [frobNormSq_unitary_eq_one _ (huc.unitaryA a)]; exact one_ne_zero,
    B_pos := fun b => by rw [frobNormSq_unitary_eq_one _ (huc.unitaryB b)]; exact one_ne_zero,
    C_pos := fun c => by rw [frobNormSq_unitary_eq_one _ (huc.unitaryC c)]; exact one_ne_zero }
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact perfectCollinearity_uniformScale_cubeRoot t ht Θ f huc.collinear hnd_Θ
  · exact factorizes_uniformScale_cubeRoot t ht Θ f huc.feasible
  · intro a
    show (t • Θ.A a) * (t • Θ.A a).conjTranspose = 1
    exact unitarity_preserved_under_unit_scale t (Θ.A a) h_norm (huc.unitaryA a)
  · intro b
    show (t • Θ.B b) * (t • Θ.B b).conjTranspose = 1
    exact unitarity_preserved_under_unit_scale t (Θ.B b) h_norm (huc.unitaryB b)
  · intro c
    show (t • Θ.C c) * (t • Θ.C c).conjTranspose = 1
    exact unitarity_preserved_under_unit_scale t (Θ.C c) h_norm (huc.unitaryC c)

/-- Composite: `UnitaryCollinear` is preserved under unitary conjugation AND
    cube-root uniform scaling. -/
theorem unitaryCollinear_unitaryConj_uniformScale_cubeRoot (t : ℂ) (ht : t ^ 3 = 1)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U * U.conjTranspose = 1)
    (Θ : HCParams n) (f : BinOp n) (huc : UnitaryCollinear Θ f) :
    UnitaryCollinear (unitaryConjAction U (uniformScale t Θ)) f := by
  exact unitaryCollinear_unitaryConjAction U hU _ f
    (unitaryCollinear_uniformScale_cubeRoot t ht Θ f huc)

/-! ## Penalty invariance under unit-modulus per-slot gauge -/

/-- Unit-modulus elements of ℂ are nonzero. -/
private lemma ne_zero_of_unit_mod {z : ℂ} (h : z * starRingEnd ℂ z = 1) : z ≠ 0 := by
  intro hz
  rw [hz, zero_mul] at h
  exact zero_ne_one h

/-- `inverseScalePenalty` is invariant under per-slot scaling by unit-modulus factors:
    `|sA|² = |sB|² = |sC|² = 1`. The cocycle condition is not needed because
    `inverseScalePenalty` already only sums over `c = f.op a b` and `T·conj T` is the
    only place the combined product `sA·sB·sC` appears, which has unit modulus too. -/
theorem inverseScalePenalty_unit_gauge (sA sB sC : Fin n → ℂ)
    (hA : ∀ a : Fin n, sA a * starRingEnd ℂ (sA a) = 1)
    (hB : ∀ b : Fin n, sB b * starRingEnd ℂ (sB b) = 1)
    (hC : ∀ c : Fin n, sC c * starRingEnd ℂ (sC c) = 1)
    (Θ : HCParams n) (f : BinOp n) :
    inverseScalePenalty (gaugeAction sA sB sC Θ) f = inverseScalePenalty Θ f := by
  unfold inverseScalePenalty
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  set c := f.op a b
  show hcProduct (gaugeAction sA sB sC Θ) a b c *
        starRingEnd ℂ (hcProduct (gaugeAction sA sB sC Θ) a b c) *
        (1 / frobNormSq ((gaugeAction sA sB sC Θ).A a) +
         1 / frobNormSq ((gaugeAction sA sB sC Θ).B b) +
         1 / frobNormSq ((gaugeAction sA sB sC Θ).C c)) = _
  rw [hcProduct_gaugeAction, frobNormSq_gaugeAction_A, frobNormSq_gaugeAction_B,
      frobNormSq_gaugeAction_C, map_mul, map_mul, map_mul]
  rw [hA a, hB b, hC c]
  simp only [one_mul]
  -- Goal now: (sA·sB·sC·T) · (conj sA · conj sB · conj sC · conj T) · (1/‖A‖² + ...)
  --         = T · conj T · (1/‖A‖² + ...)
  congr 1
  -- (sA·sB·sC·T) · (conj sA · conj sB · conj sC · conj T) = T · conj T
  rw [show
    sA a * sB b * sC c * hcProduct Θ a b c *
    (starRingEnd ℂ (sA a) * starRingEnd ℂ (sB b) * starRingEnd ℂ (sC c) *
     starRingEnd ℂ (hcProduct Θ a b c)) =
    (sA a * starRingEnd ℂ (sA a)) * (sB b * starRingEnd ℂ (sB b)) *
    (sC c * starRingEnd ℂ (sC c)) *
    (hcProduct Θ a b c * starRingEnd ℂ (hcProduct Θ a b c)) from by ring]
  rw [hA a, hB b, hC c, one_mul, one_mul, one_mul]

/-- `misalignmentPenalty` is invariant under per-slot scaling by unit-modulus factors,
    via the decomposition + objective invariance. Requires the cocycle condition
    on support to apply `objective_invariant_under_unit_gauge`. -/
theorem misalignmentPenalty_unit_gauge (sA sB sC : Fin n → ℂ)
    (hA : ∀ a : Fin n, sA a * starRingEnd ℂ (sA a) = 1)
    (hB : ∀ b : Fin n, sB b * starRingEnd ℂ (sB b) = 1)
    (hC : ∀ c : Fin n, sC c * starRingEnd ℂ (sC c) = 1)
    (Θ : HCParams n) (f : BinOp n) (hnd : Nondegenerate Θ) :
    misalignmentPenalty (gaugeAction sA sB sC Θ) f = misalignmentPenalty Θ f := by
  -- gaugeAction by unit-modulus factors preserves Nondegenerate.
  have hnd' : Nondegenerate (gaugeAction sA sB sC Θ) :=
    nondegenerate_gaugeAction _ _ _
      (fun a => ne_zero_of_unit_mod (hA a))
      (fun b => ne_zero_of_unit_mod (hB b))
      (fun c => ne_zero_of_unit_mod (hC c)) hnd
  have h_obj : objective (gaugeAction sA sB sC Θ) f = objective Θ f :=
    objective_invariant_under_unit_gauge sA sB sC Θ f hA hB hC
  have h_ip : inverseScalePenalty (gaugeAction sA sB sC Θ) f = inverseScalePenalty Θ f :=
    inverseScalePenalty_unit_gauge sA sB sC hA hB hC Θ f
  have h_dec : objective Θ f = inverseScalePenalty Θ f + misalignmentPenalty Θ f :=
    decomposition Θ f hnd
  have h_dec' : objective (gaugeAction sA sB sC Θ) f =
      inverseScalePenalty (gaugeAction sA sB sC Θ) f +
      misalignmentPenalty (gaugeAction sA sB sC Θ) f :=
    decomposition (gaugeAction sA sB sC Θ) f hnd'
  have key : inverseScalePenalty Θ f + misalignmentPenalty (gaugeAction sA sB sC Θ) f =
      inverseScalePenalty Θ f + misalignmentPenalty Θ f := by
    calc inverseScalePenalty Θ f + misalignmentPenalty (gaugeAction sA sB sC Θ) f
        = inverseScalePenalty (gaugeAction sA sB sC Θ) f +
            misalignmentPenalty (gaugeAction sA sB sC Θ) f := by rw [h_ip]
      _ = objective (gaugeAction sA sB sC Θ) f := h_dec'.symm
      _ = objective Θ f := h_obj
      _ = inverseScalePenalty Θ f + misalignmentPenalty Θ f := h_dec
  exact add_left_cancel key

/-- `PerfectCollinearity` is preserved under unit-modulus per-slot gauge action. -/
theorem perfectCollinearity_unit_gauge (sA sB sC : Fin n → ℂ)
    (hA : ∀ a : Fin n, sA a * starRingEnd ℂ (sA a) = 1)
    (hB : ∀ b : Fin n, sB b * starRingEnd ℂ (sB b) = 1)
    (hC : ∀ c : Fin n, sC c * starRingEnd ℂ (sC c) = 1)
    (Θ : HCParams n) (f : BinOp n)
    (hcol : PerfectCollinearity Θ f) (hnd : Nondegenerate Θ) :
    PerfectCollinearity (gaugeAction sA sB sC Θ) f := by
  show misalignmentPenalty (gaugeAction sA sB sC Θ) f = 0
  rw [misalignmentPenalty_unit_gauge sA sB sC hA hB hC Θ f hnd]
  exact hcol

/-- The trifecta PCFN (PerfectCollinearity + Factorizes + Nondegenerate) is preserved
    under unit-modulus per-slot gauge satisfying the support cocycle. -/
theorem PCFN_unit_gauge (sA sB sC : Fin n → ℂ) (Θ : HCParams n) (f : BinOp n)
    (hA : ∀ a : Fin n, sA a * starRingEnd ℂ (sA a) = 1)
    (hB : ∀ b : Fin n, sB b * starRingEnd ℂ (sB b) = 1)
    (hC : ∀ c : Fin n, sC c * starRingEnd ℂ (sC c) = 1)
    (h_cocycle : ∀ a b : Fin n, sA a * sB b * sC (f.op a b) = 1)
    (hcol : PerfectCollinearity Θ f) (hfeas : Factorizes Θ f)
    (hnd : Nondegenerate Θ) :
    PerfectCollinearity (gaugeAction sA sB sC Θ) f ∧
    Factorizes (gaugeAction sA sB sC Θ) f ∧
    Nondegenerate (gaugeAction sA sB sC Θ) := by
  refine ⟨?_, ?_, ?_⟩
  · exact perfectCollinearity_unit_gauge sA sB sC hA hB hC Θ f hcol hnd
  · exact (factorizes_gaugeAction_iff sA sB sC Θ f hfeas).mpr h_cocycle
  · exact nondegenerate_gaugeAction _ _ _
      (fun a => ne_zero_of_unit_mod (hA a))
      (fun b => ne_zero_of_unit_mod (hB b))
      (fun c => ne_zero_of_unit_mod (hC c)) hnd

/-- `|hcProduct|² = T · conj T` is invariant under unit-modulus per-slot gauge
    (no cocycle condition needed — only per-slot unit modulus). -/
theorem hcProduct_normSq_unit_gauge (sA sB sC : Fin n → ℂ)
    (hA : ∀ a : Fin n, sA a * starRingEnd ℂ (sA a) = 1)
    (hB : ∀ b : Fin n, sB b * starRingEnd ℂ (sB b) = 1)
    (hC : ∀ c : Fin n, sC c * starRingEnd ℂ (sC c) = 1)
    (Θ : HCParams n) (a b c : Fin n) :
    hcProduct (gaugeAction sA sB sC Θ) a b c *
      starRingEnd ℂ (hcProduct (gaugeAction sA sB sC Θ) a b c) =
    hcProduct Θ a b c * starRingEnd ℂ (hcProduct Θ a b c) := by
  rw [hcProduct_gaugeAction, map_mul, map_mul, map_mul]
  -- Goal: (sA·sB·sC·T) · (conj sA · conj sB · conj sC · conj T) = T · conj T
  rw [show
    sA a * sB b * sC c * hcProduct Θ a b c *
    (starRingEnd ℂ (sA a) * starRingEnd ℂ (sB b) * starRingEnd ℂ (sC c) *
     starRingEnd ℂ (hcProduct Θ a b c)) =
    (sA a * starRingEnd ℂ (sA a)) * (sB b * starRingEnd ℂ (sB b)) *
    (sC c * starRingEnd ℂ (sC c)) *
    (hcProduct Θ a b c * starRingEnd ℂ (hcProduct Θ a b c)) from by ring]
  rw [hA a, hB b, hC c, one_mul, one_mul, one_mul]

/-- `kappaTriple` is invariant under unit-modulus per-slot gauge action — corollary
    of `kappaTriple_gaugeAction` since unit-modulus implies nonzero. -/
theorem kappaTriple_unit_gauge (sA sB sC : Fin n → ℂ)
    (hA : ∀ a : Fin n, sA a * starRingEnd ℂ (sA a) = 1)
    (hB : ∀ b : Fin n, sB b * starRingEnd ℂ (sB b) = 1)
    (hC : ∀ c : Fin n, sC c * starRingEnd ℂ (sC c) = 1)
    (Θ : HCParams n) (a b c : Fin n) :
    kappaTriple (gaugeAction sA sB sC Θ) a b c = kappaTriple Θ a b c :=
  kappaTriple_gaugeAction sA sB sC
    (fun a => ne_zero_of_unit_mod (hA a))
    (fun b => ne_zero_of_unit_mod (hB b))
    (fun c => ne_zero_of_unit_mod (hC c)) Θ a b c

/-- `hcNormSq` is invariant under per-slot unit-modulus gauge: each slice keeps
    its Frobenius norm-squared. -/
theorem hcNormSq_unit_gauge (sA sB sC : Fin n → ℂ)
    (hA : ∀ a : Fin n, sA a * starRingEnd ℂ (sA a) = 1)
    (hB : ∀ b : Fin n, sB b * starRingEnd ℂ (sB b) = 1)
    (hC : ∀ c : Fin n, sC c * starRingEnd ℂ (sC c) = 1)
    (Θ : HCParams n) :
    Tikhonov.hcNormSq (gaugeAction sA sB sC Θ) = Tikhonov.hcNormSq Θ := by
  rw [hcNormSq_gaugeAction]
  unfold Tikhonov.hcNormSq
  congr 1
  · congr 1
    · apply Finset.sum_congr rfl
      intro a _
      rw [hA a, one_mul]
    · apply Finset.sum_congr rfl
      intro b _
      rw [hB b, one_mul]
  · apply Finset.sum_congr rfl
    intro c _
    rw [hC c, one_mul]

/-- Combined: `hcNormSq` is invariant under unit-modulus per-slot gauge AND
    unitary conjugation. -/
theorem hcNormSq_unitaryConj_unit_gauge (sA sB sC : Fin n → ℂ)
    (hA : ∀ a : Fin n, sA a * starRingEnd ℂ (sA a) = 1)
    (hB : ∀ b : Fin n, sB b * starRingEnd ℂ (sB b) = 1)
    (hC : ∀ c : Fin n, sC c * starRingEnd ℂ (sC c) = 1)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U * U.conjTranspose = 1) (Θ : HCParams n) :
    Tikhonov.hcNormSq (unitaryConjAction U (gaugeAction sA sB sC Θ)) =
    Tikhonov.hcNormSq Θ := by
  rw [hcNormSq_unitaryConjAction U hU, hcNormSq_unit_gauge sA sB sC hA hB hC]

/-- `UnitaryCollinear` is preserved under unit-modulus per-slot gauge
    satisfying the support cocycle. The unitarity of each slice is preserved
    because |sX|² = 1 implies (sX·M)(sX·M)ᴴ = M·Mᴴ. -/
theorem unitaryCollinear_unit_gauge (sA sB sC : Fin n → ℂ) (Θ : HCParams n) (f : BinOp n)
    (hA : ∀ a : Fin n, sA a * starRingEnd ℂ (sA a) = 1)
    (hB : ∀ b : Fin n, sB b * starRingEnd ℂ (sB b) = 1)
    (hC : ∀ c : Fin n, sC c * starRingEnd ℂ (sC c) = 1)
    (h_cocycle : ∀ a b : Fin n, sA a * sB b * sC (f.op a b) = 1)
    (huc : UnitaryCollinear Θ f) :
    UnitaryCollinear (gaugeAction sA sB sC Θ) f := by
  -- Recover Nondegenerate from unitarity of slices.
  have hnd_Θ : Nondegenerate Θ := {
    A_pos := fun a => by rw [frobNormSq_unitary_eq_one _ (huc.unitaryA a)]; exact one_ne_zero,
    B_pos := fun b => by rw [frobNormSq_unitary_eq_one _ (huc.unitaryB b)]; exact one_ne_zero,
    C_pos := fun c => by rw [frobNormSq_unitary_eq_one _ (huc.unitaryC c)]; exact one_ne_zero }
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact perfectCollinearity_unit_gauge sA sB sC hA hB hC Θ f huc.collinear hnd_Θ
  · exact (factorizes_gaugeAction_iff sA sB sC Θ f huc.feasible).mpr h_cocycle
  · intro a
    show (sA a • Θ.A a) * (sA a • Θ.A a).conjTranspose = 1
    exact unitarity_preserved_under_unit_scale (sA a) (Θ.A a) (hA a) (huc.unitaryA a)
  · intro b
    show (sB b • Θ.B b) * (sB b • Θ.B b).conjTranspose = 1
    exact unitarity_preserved_under_unit_scale (sB b) (Θ.B b) (hB b) (huc.unitaryB b)
  · intro c
    show (sC c • Θ.C c) * (sC c • Θ.C c).conjTranspose = 1
    exact unitarity_preserved_under_unit_scale (sC c) (Θ.C c) (hC c) (huc.unitaryC c)

/-! ## Combined unitary + unit-modulus per-slot gauge orbit preservation -/

/-- The full combined gauge action: unitary conjugation composed with per-slot
    unit-modulus scaling that satisfies the support cocycle. This is the
    most general continuous gauge symmetry of the hyper-cube objective. -/
theorem PCFN_unitaryConj_unit_gauge (sA sB sC : Fin n → ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ) (Θ : HCParams n) (f : BinOp n)
    (hA : ∀ a : Fin n, sA a * starRingEnd ℂ (sA a) = 1)
    (hB : ∀ b : Fin n, sB b * starRingEnd ℂ (sB b) = 1)
    (hC : ∀ c : Fin n, sC c * starRingEnd ℂ (sC c) = 1)
    (h_cocycle : ∀ a b : Fin n, sA a * sB b * sC (f.op a b) = 1)
    (hU : U * U.conjTranspose = 1)
    (hcol : PerfectCollinearity Θ f) (hfeas : Factorizes Θ f)
    (hnd : Nondegenerate Θ) :
    PerfectCollinearity (unitaryConjAction U (gaugeAction sA sB sC Θ)) f ∧
    Factorizes (unitaryConjAction U (gaugeAction sA sB sC Θ)) f ∧
    Nondegenerate (unitaryConjAction U (gaugeAction sA sB sC Θ)) := by
  obtain ⟨hcol1, hfeas1, hnd1⟩ :=
    PCFN_unit_gauge sA sB sC Θ f hA hB hC h_cocycle hcol hfeas hnd
  exact PCFN_unitaryConjAction U hU _ f hcol1 hfeas1 hnd1

/-- `UnitaryCollinear` is preserved under the combined unitary + unit-modulus
    per-slot gauge with cocycle. -/
theorem unitaryCollinear_unitaryConj_unit_gauge (sA sB sC : Fin n → ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ) (Θ : HCParams n) (f : BinOp n)
    (hA : ∀ a : Fin n, sA a * starRingEnd ℂ (sA a) = 1)
    (hB : ∀ b : Fin n, sB b * starRingEnd ℂ (sB b) = 1)
    (hC : ∀ c : Fin n, sC c * starRingEnd ℂ (sC c) = 1)
    (h_cocycle : ∀ a b : Fin n, sA a * sB b * sC (f.op a b) = 1)
    (hU : U * U.conjTranspose = 1)
    (huc : UnitaryCollinear Θ f) :
    UnitaryCollinear (unitaryConjAction U (gaugeAction sA sB sC Θ)) f := by
  exact unitaryCollinear_unitaryConjAction U hU _ f
    (unitaryCollinear_unit_gauge sA sB sC Θ f hA hB hC h_cocycle huc)

/-- objective is invariant under the combined unitary + unit-modulus per-slot
    gauge (no cocycle needed for the objective). -/
theorem objective_unitaryConj_unit_gauge (sA sB sC : Fin n → ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ) (Θ : HCParams n) (f : BinOp n)
    (hA : ∀ a : Fin n, sA a * starRingEnd ℂ (sA a) = 1)
    (hB : ∀ b : Fin n, sB b * starRingEnd ℂ (sB b) = 1)
    (hC : ∀ c : Fin n, sC c * starRingEnd ℂ (sC c) = 1)
    (hU : U * U.conjTranspose = 1) :
    objective (unitaryConjAction U (gaugeAction sA sB sC Θ)) f = objective Θ f := by
  rw [objective_unitaryConjAction U hU,
      objective_invariant_under_unit_gauge sA sB sC Θ f hA hB hC]

/-! ## combinedGauge: the full gauge action -/

/-- The combined gauge action: per-slot complex scaling followed by unitary
    conjugation. This packages the two commuting gauge actions into a single
    operation that can be composed and inverted. -/
noncomputable def combinedGauge (U : Matrix (Fin n) (Fin n) ℂ) (sA sB sC : Fin n → ℂ)
    (Θ : HCParams n) : HCParams n :=
  unitaryConjAction U (gaugeAction sA sB sC Θ)

/-- Trivial combinedGauge (`U = 1`, all factors = 1) is the identity. -/
@[simp] theorem combinedGauge_one (Θ : HCParams n) :
    combinedGauge 1 (fun _ => (1 : ℂ)) (fun _ => 1) (fun _ => 1) Θ = Θ := by
  unfold combinedGauge
  rw [gaugeAction_one, unitaryConjAction_one]

/-- The combined gauge is the same as gauge-then-unitary (commutativity). -/
theorem combinedGauge_eq_gaugeAction_unitaryConj (U : Matrix (Fin n) (Fin n) ℂ)
    (sA sB sC : Fin n → ℂ) (Θ : HCParams n) :
    combinedGauge U sA sB sC Θ = gaugeAction sA sB sC (unitaryConjAction U Θ) := by
  unfold combinedGauge
  exact gaugeAction_unitaryConjAction_comm sA sB sC U Θ

/-- Composition formula: applying two combined gauges in sequence is equivalent
    to one combined gauge with multiplicatively composed factors. -/
theorem combinedGauge_mul (U₁ U₂ : Matrix (Fin n) (Fin n) ℂ)
    (sA₁ sB₁ sC₁ sA₂ sB₂ sC₂ : Fin n → ℂ) (Θ : HCParams n) :
    combinedGauge U₂ sA₂ sB₂ sC₂ (combinedGauge U₁ sA₁ sB₁ sC₁ Θ) =
    combinedGauge (U₂ * U₁) (fun a => sA₂ a * sA₁ a) (fun b => sB₂ b * sB₁ b)
      (fun c => sC₂ c * sC₁ c) Θ := by
  unfold combinedGauge
  -- LHS: unitaryConjAction U₂ (gaugeAction s₂ (unitaryConjAction U₁ (gaugeAction s₁ Θ)))
  -- Apply comm to swap inner gaugeAction past unitaryConjAction U₁:
  rw [← gaugeAction_unitaryConjAction_comm sA₂ sB₂ sC₂ U₁ (gaugeAction sA₁ sB₁ sC₁ Θ)]
  -- LHS: unitaryConjAction U₂ (unitaryConjAction U₁ (gaugeAction s₂ (gaugeAction s₁ Θ)))
  rw [unitaryConjAction_mul, gaugeAction_mul]

/-- Inversion: combinedGauge with inverted factors undoes the original action,
    when `U` is unitary and per-slot factors are nonzero. -/
theorem combinedGauge_inv (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1)
    (sA sB sC : Fin n → ℂ) (hA : ∀ a, sA a ≠ 0) (hB : ∀ b, sB b ≠ 0) (hC : ∀ c, sC c ≠ 0)
    (Θ : HCParams n) :
    combinedGauge U.conjTranspose
      (fun a => (sA a)⁻¹) (fun b => (sB b)⁻¹) (fun c => (sC c)⁻¹)
      (combinedGauge U sA sB sC Θ) = Θ := by
  unfold combinedGauge
  -- Apply comm: gaugeAction (s⁻¹) (unitaryConjAction U† (...)) = unitaryConjAction U† (gaugeAction (s⁻¹) (...))
  rw [← gaugeAction_unitaryConjAction_comm]
  -- = unitaryConjAction U† (unitaryConjAction U (gaugeAction (s⁻¹) (gaugeAction s Θ)))
  rw [unitaryConjAction_inv U hU, gaugeAction_inv sA sB sC hA hB hC]

/-! ## combinedGauge orbit -/

/-- The orbit of `Θ` under the combined unit-modulus per-slot × unitary gauge action. -/
def combinedGaugeOrbit (Θ : HCParams n) : Set (HCParams n) :=
  { Ψ | ∃ (U : Matrix (Fin n) (Fin n) ℂ) (sA sB sC : Fin n → ℂ),
        (∀ a, sA a * starRingEnd ℂ (sA a) = 1) ∧
        (∀ b, sB b * starRingEnd ℂ (sB b) = 1) ∧
        (∀ c, sC c * starRingEnd ℂ (sC c) = 1) ∧
        U * U.conjTranspose = 1 ∧
        Ψ = combinedGauge U sA sB sC Θ }

/-- The combined orbit always contains `Θ` itself (`U = 1`, `s = 1`). -/
theorem mem_combinedGaugeOrbit_self (Θ : HCParams n) :
    Θ ∈ combinedGaugeOrbit Θ := by
  refine ⟨1, fun _ => 1, fun _ => 1, fun _ => 1, ?_, ?_, ?_, ?_, ?_⟩
  · intro a; rw [map_one]; ring
  · intro b; rw [map_one]; ring
  · intro c; rw [map_one]; ring
  · simp
  · rw [combinedGauge_one]

/-- `objective` is constant on the combined gauge orbit. -/
theorem objective_constant_on_combinedGaugeOrbit (Θ Ψ : HCParams n) (f : BinOp n)
    (h : Ψ ∈ combinedGaugeOrbit Θ) :
    objective Ψ f = objective Θ f := by
  obtain ⟨U, sA, sB, sC, hA, hB, hC, hU, hΨ⟩ := h
  rw [hΨ]
  unfold combinedGauge
  exact objective_unitaryConj_unit_gauge sA sB sC U Θ f hA hB hC hU

/-- `hcNormSq` is constant on the combined gauge orbit. -/
theorem hcNormSq_constant_on_combinedGaugeOrbit (Θ Ψ : HCParams n)
    (h : Ψ ∈ combinedGaugeOrbit Θ) :
    Tikhonov.hcNormSq Ψ = Tikhonov.hcNormSq Θ := by
  obtain ⟨U, sA, sB, sC, hA, hB, hC, hU, hΨ⟩ := h
  rw [hΨ]
  unfold combinedGauge
  exact hcNormSq_unitaryConj_unit_gauge sA sB sC hA hB hC U hU Θ

/-- `kappaTriple` is constant on the combined gauge orbit. -/
theorem kappaTriple_constant_on_combinedGaugeOrbit (Θ Ψ : HCParams n)
    (h : Ψ ∈ combinedGaugeOrbit Θ) (a b c : Fin n) :
    kappaTriple Ψ a b c = kappaTriple Θ a b c := by
  obtain ⟨U, sA, sB, sC, hA, hB, hC, hU, hΨ⟩ := h
  rw [hΨ]
  unfold combinedGauge
  rw [kappaTriple_unitaryConjAction U hU,
      kappaTriple_unit_gauge sA sB sC hA hB hC]

/-- The inverse of a unit-modulus `z` is also unit-modulus. -/
private lemma inv_unit_mod {z : ℂ} (h : z * starRingEnd ℂ z = 1) :
    z⁻¹ * starRingEnd ℂ z⁻¹ = 1 := by
  have hz : z ≠ 0 := ne_zero_of_unit_mod h
  rw [map_inv₀]
  rw [show z⁻¹ * (starRingEnd ℂ z)⁻¹ = (z * starRingEnd ℂ z)⁻¹ from
        (mul_inv (z) (starRingEnd ℂ z)).symm]
  rw [h, inv_one]

/-- The product of two unit-modulus elements is unit-modulus. -/
private lemma mul_unit_mod {z w : ℂ}
    (hz : z * starRingEnd ℂ z = 1) (hw : w * starRingEnd ℂ w = 1) :
    (z * w) * starRingEnd ℂ (z * w) = 1 := by
  rw [map_mul]
  rw [show z * w * (starRingEnd ℂ z * starRingEnd ℂ w) =
        (z * starRingEnd ℂ z) * (w * starRingEnd ℂ w) from by ring]
  rw [hz, hw, mul_one]

/-- The conjugate transpose of a unitary matrix is unitary. -/
private lemma unitary_conjTranspose {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : U * U.conjTranspose = 1) :
    U.conjTranspose * U.conjTranspose.conjTranspose = 1 := by
  rw [Matrix.conjTranspose_conjTranspose]
  exact mul_eq_one_comm.mp hU

/-- The product of two unitary matrices is unitary. -/
private lemma unitary_mul {U V : Matrix (Fin n) (Fin n) ℂ}
    (hU : U * U.conjTranspose = 1) (hV : V * V.conjTranspose = 1) :
    (U * V) * (U * V).conjTranspose = 1 := by
  rw [Matrix.conjTranspose_mul]
  rw [show U * V * (V.conjTranspose * U.conjTranspose) =
        U * (V * V.conjTranspose) * U.conjTranspose from by
    simp only [Matrix.mul_assoc]]
  rw [hV, Matrix.mul_one, hU]

/-- Symmetry: if `Ψ` is in the combined gauge orbit of `Θ`, then `Θ` is in the
    combined gauge orbit of `Ψ`. The inverse gauge action uses the conjugate
    transpose for unitary and componentwise inverse for per-slot factors. -/
theorem combinedGaugeOrbit_symm {Θ Ψ : HCParams n}
    (h : Ψ ∈ combinedGaugeOrbit Θ) : Θ ∈ combinedGaugeOrbit Ψ := by
  obtain ⟨U, sA, sB, sC, hA, hB, hC, hU, hΨ⟩ := h
  refine ⟨U.conjTranspose, fun a => (sA a)⁻¹, fun b => (sB b)⁻¹, fun c => (sC c)⁻¹,
    fun a => inv_unit_mod (hA a),
    fun b => inv_unit_mod (hB b),
    fun c => inv_unit_mod (hC c),
    unitary_conjTranspose hU, ?_⟩
  rw [hΨ]
  exact (combinedGauge_inv U hU sA sB sC
    (fun a => ne_zero_of_unit_mod (hA a))
    (fun b => ne_zero_of_unit_mod (hB b))
    (fun c => ne_zero_of_unit_mod (hC c)) Θ).symm

/-- Transitivity: combined gauge orbit membership chains. -/
theorem combinedGaugeOrbit_trans {Θ Ψ Φ : HCParams n}
    (h₁ : Ψ ∈ combinedGaugeOrbit Θ) (h₂ : Φ ∈ combinedGaugeOrbit Ψ) :
    Φ ∈ combinedGaugeOrbit Θ := by
  obtain ⟨U₁, sA₁, sB₁, sC₁, hA₁, hB₁, hC₁, hU₁, hΨ⟩ := h₁
  obtain ⟨U₂, sA₂, sB₂, sC₂, hA₂, hB₂, hC₂, hU₂, hΦ⟩ := h₂
  refine ⟨U₂ * U₁,
    fun a => sA₂ a * sA₁ a, fun b => sB₂ b * sB₁ b, fun c => sC₂ c * sC₁ c,
    fun a => mul_unit_mod (hA₂ a) (hA₁ a),
    fun b => mul_unit_mod (hB₂ b) (hB₁ b),
    fun c => mul_unit_mod (hC₂ c) (hC₁ c),
    unitary_mul hU₂ hU₁, ?_⟩
  rw [hΦ, hΨ]
  exact combinedGauge_mul U₁ U₂ sA₁ sB₁ sC₁ sA₂ sB₂ sC₂ Θ

/-! ## combinedGauge Setoid + quotient + descent -/

/-- The combined gauge orbit gives an equivalence relation on `HCParams n`. -/
def combinedGaugeSetoid (n : ℕ) [NeZero n] : Setoid (HCParams n) where
  r Θ Ψ := Ψ ∈ combinedGaugeOrbit Θ
  iseqv :=
    ⟨mem_combinedGaugeOrbit_self,
     combinedGaugeOrbit_symm,
     combinedGaugeOrbit_trans⟩

/-- The quotient of `HCParams n` by the combined gauge equivalence relation. -/
def CombinedGaugeQuotient (n : ℕ) [NeZero n] : Type :=
  Quotient (combinedGaugeSetoid n)

/-- The `objective` function descends to the combined gauge quotient: equivalent
    parameters give the same objective value. -/
theorem objective_descends_to_combinedGaugeQuotient (f : BinOp n) :
    ∀ Θ Ψ : HCParams n, (combinedGaugeSetoid n).r Θ Ψ →
      objective Θ f = objective Ψ f := by
  intro Θ Ψ h
  exact (objective_constant_on_combinedGaugeOrbit Θ Ψ f h).symm

/-- The `hcNormSq` function descends to the combined gauge quotient. -/
theorem hcNormSq_descends_to_combinedGaugeQuotient :
    ∀ Θ Ψ : HCParams n, (combinedGaugeSetoid n).r Θ Ψ →
      Tikhonov.hcNormSq Θ = Tikhonov.hcNormSq Ψ := by
  intro Θ Ψ h
  exact (hcNormSq_constant_on_combinedGaugeOrbit Θ Ψ h).symm

/-- The `kappaTriple` function descends to the combined gauge quotient. -/
theorem kappaTriple_descends_to_combinedGaugeQuotient (a b c : Fin n) :
    ∀ Θ Ψ : HCParams n, (combinedGaugeSetoid n).r Θ Ψ →
      kappaTriple Θ a b c = kappaTriple Ψ a b c := by
  intro Θ Ψ h
  exact (kappaTriple_constant_on_combinedGaugeOrbit Θ Ψ h a b c).symm

/-! ## Penalty + property descents to combined gauge quotient -/

/-- `inverseScalePenalty` is constant on the combined gauge orbit. -/
theorem inverseScalePenalty_constant_on_combinedGaugeOrbit (Θ Ψ : HCParams n) (f : BinOp n)
    (h : Ψ ∈ combinedGaugeOrbit Θ) :
    inverseScalePenalty Ψ f = inverseScalePenalty Θ f := by
  obtain ⟨U, sA, sB, sC, hA, hB, hC, hU, hΨ⟩ := h
  rw [hΨ]
  unfold combinedGauge
  rw [inverseScalePenalty_unitaryConjAction U hU,
      inverseScalePenalty_unit_gauge sA sB sC hA hB hC]

/-- `inverseScalePenalty` descends to the combined gauge quotient. -/
theorem inverseScalePenalty_descends_to_combinedGaugeQuotient (f : BinOp n) :
    ∀ Θ Ψ : HCParams n, (combinedGaugeSetoid n).r Θ Ψ →
      inverseScalePenalty Θ f = inverseScalePenalty Ψ f := by
  intro Θ Ψ h
  exact (inverseScalePenalty_constant_on_combinedGaugeOrbit Θ Ψ f h).symm

/-- `Nondegenerate` is a gauge-invariant property: it descends to the quotient.
    Forward direction. -/
theorem nondegenerate_of_combinedGaugeOrbit (Θ Ψ : HCParams n)
    (h : Ψ ∈ combinedGaugeOrbit Θ) (hnd : Nondegenerate Θ) :
    Nondegenerate Ψ := by
  obtain ⟨U, sA, sB, sC, hA, hB, hC, hU, hΨ⟩ := h
  rw [hΨ]
  unfold combinedGauge
  apply nondegenerate_unitaryConjAction U hU
  exact nondegenerate_gaugeAction _ _ _
    (fun a => ne_zero_of_unit_mod (hA a))
    (fun b => ne_zero_of_unit_mod (hB b))
    (fun c => ne_zero_of_unit_mod (hC c)) hnd

/-- `Nondegenerate` is a gauge-invariant property — iff form via symmetry of the
    orbit. -/
theorem nondegenerate_iff_combinedGaugeOrbit {Θ Ψ : HCParams n}
    (h : Ψ ∈ combinedGaugeOrbit Θ) :
    Nondegenerate Θ ↔ Nondegenerate Ψ :=
  ⟨nondegenerate_of_combinedGaugeOrbit Θ Ψ h,
   nondegenerate_of_combinedGaugeOrbit Ψ Θ (combinedGaugeOrbit_symm h)⟩

/-- `misalignmentPenalty` is constant on the combined gauge orbit (requires
    Nondegenerate at the source point — which transfers to all orbit members). -/
theorem misalignmentPenalty_constant_on_combinedGaugeOrbit (Θ Ψ : HCParams n) (f : BinOp n)
    (h : Ψ ∈ combinedGaugeOrbit Θ) (hnd : Nondegenerate Θ) :
    misalignmentPenalty Ψ f = misalignmentPenalty Θ f := by
  obtain ⟨U, sA, sB, sC, hA, hB, hC, hU, hΨ⟩ := h
  rw [hΨ]
  unfold combinedGauge
  -- gaugeAction by unit-modulus preserves Nondegenerate.
  have hnd_gauge : Nondegenerate (gaugeAction sA sB sC Θ) :=
    nondegenerate_gaugeAction _ _ _
      (fun a => ne_zero_of_unit_mod (hA a))
      (fun b => ne_zero_of_unit_mod (hB b))
      (fun c => ne_zero_of_unit_mod (hC c)) hnd
  rw [misalignmentPenalty_unitaryConjAction U hU _ f hnd_gauge
        (nondegenerate_unitaryConjAction U hU _ hnd_gauge)]
  exact misalignmentPenalty_unit_gauge sA sB sC hA hB hC Θ f hnd

/-- `PerfectCollinearity` is invariant under the combined gauge orbit. -/
theorem perfectCollinearity_of_combinedGaugeOrbit {Θ Ψ : HCParams n} (f : BinOp n)
    (h : Ψ ∈ combinedGaugeOrbit Θ) (hcol : PerfectCollinearity Θ f)
    (hnd : Nondegenerate Θ) :
    PerfectCollinearity Ψ f := by
  show misalignmentPenalty Ψ f = 0
  rw [misalignmentPenalty_constant_on_combinedGaugeOrbit Θ Ψ f h hnd]
  exact hcol

/-! ## feasibleCombinedGaugeOrbit (with support cocycle) preserves Factorizes -/

/-- The feasibility-preserving combined gauge orbit: combined gauge orbit
    members whose per-slot factors additionally satisfy the support cocycle
    `sA(a) · sB(b) · sC(f.op a b) = 1`. This is the gauge subgroup that
    preserves Factorizes. -/
def feasibleCombinedGaugeOrbit (Θ : HCParams n) (f : BinOp n) : Set (HCParams n) :=
  { Ψ | ∃ (U : Matrix (Fin n) (Fin n) ℂ) (sA sB sC : Fin n → ℂ),
        (∀ a, sA a * starRingEnd ℂ (sA a) = 1) ∧
        (∀ b, sB b * starRingEnd ℂ (sB b) = 1) ∧
        (∀ c, sC c * starRingEnd ℂ (sC c) = 1) ∧
        (∀ a b, sA a * sB b * sC (f.op a b) = 1) ∧
        U * U.conjTranspose = 1 ∧
        Ψ = combinedGauge U sA sB sC Θ }

/-- The feasibility-preserving orbit is contained in the full combined gauge orbit. -/
theorem feasibleCombinedGaugeOrbit_subset (Θ : HCParams n) (f : BinOp n) :
    feasibleCombinedGaugeOrbit Θ f ⊆ combinedGaugeOrbit Θ := by
  intro Ψ ⟨U, sA, sB, sC, hA, hB, hC, _, hU, hΨ⟩
  exact ⟨U, sA, sB, sC, hA, hB, hC, hU, hΨ⟩

/-- The feasibility-preserving orbit always contains `Θ` itself: trivial gauge
    `(U=1, s=1)` automatically satisfies the cocycle `1·1·1 = 1`. -/
theorem mem_feasibleCombinedGaugeOrbit_self (Θ : HCParams n) (f : BinOp n) :
    Θ ∈ feasibleCombinedGaugeOrbit Θ f := by
  refine ⟨1, fun _ => 1, fun _ => 1, fun _ => 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a; rw [map_one]; ring
  · intro b; rw [map_one]; ring
  · intro c; rw [map_one]; ring
  · intro a b; ring
  · simp
  · rw [combinedGauge_one]

/-- `Factorizes` is preserved on the feasibility-preserving combined gauge orbit. -/
theorem factorizes_of_feasibleCombinedGaugeOrbit {Θ Ψ : HCParams n} (f : BinOp n)
    (h : Ψ ∈ feasibleCombinedGaugeOrbit Θ f) (hfeas : Factorizes Θ f) :
    Factorizes Ψ f := by
  obtain ⟨U, sA, sB, sC, hA, hB, hC, h_cocycle, hU, hΨ⟩ := h
  rw [hΨ]
  unfold combinedGauge
  apply factorizes_unitaryConjAction _ _ _ U hU
  exact (factorizes_gaugeAction_iff sA sB sC Θ f hfeas).mpr h_cocycle

/-- The PCFN trifecta is preserved on the feasibility-preserving combined gauge orbit. -/
theorem PCFN_of_feasibleCombinedGaugeOrbit {Θ Ψ : HCParams n} (f : BinOp n)
    (h : Ψ ∈ feasibleCombinedGaugeOrbit Θ f) (hcol : PerfectCollinearity Θ f)
    (hfeas : Factorizes Θ f) (hnd : Nondegenerate Θ) :
    PerfectCollinearity Ψ f ∧ Factorizes Ψ f ∧ Nondegenerate Ψ := by
  have h_combined : Ψ ∈ combinedGaugeOrbit Θ :=
    feasibleCombinedGaugeOrbit_subset Θ f h
  refine ⟨?_, ?_, ?_⟩
  · exact perfectCollinearity_of_combinedGaugeOrbit f h_combined hcol hnd
  · exact factorizes_of_feasibleCombinedGaugeOrbit f h hfeas
  · exact nondegenerate_of_combinedGaugeOrbit Θ Ψ h_combined hnd

/-- `UnitaryCollinear` is preserved on the feasibility-preserving combined gauge orbit. -/
theorem unitaryCollinear_of_feasibleCombinedGaugeOrbit {Θ Ψ : HCParams n} (f : BinOp n)
    (h : Ψ ∈ feasibleCombinedGaugeOrbit Θ f) (huc : UnitaryCollinear Θ f) :
    UnitaryCollinear Ψ f := by
  obtain ⟨U, sA, sB, sC, hA, hB, hC, h_cocycle, hU, hΨ⟩ := h
  rw [hΨ]
  unfold combinedGauge
  exact unitaryCollinear_unitaryConjAction U hU _ f
    (unitaryCollinear_unit_gauge sA sB sC Θ f hA hB hC h_cocycle huc)

/-- Symmetry of `feasibleCombinedGaugeOrbit`: the inverse gauge factors preserve
    the support cocycle (the inverse of `1` is `1`). -/
theorem feasibleCombinedGaugeOrbit_symm {Θ Ψ : HCParams n} {f : BinOp n}
    (h : Ψ ∈ feasibleCombinedGaugeOrbit Θ f) :
    Θ ∈ feasibleCombinedGaugeOrbit Ψ f := by
  obtain ⟨U, sA, sB, sC, hA, hB, hC, h_cocycle, hU, hΨ⟩ := h
  refine ⟨U.conjTranspose,
    fun a => (sA a)⁻¹, fun b => (sB b)⁻¹, fun c => (sC c)⁻¹,
    fun a => inv_unit_mod (hA a),
    fun b => inv_unit_mod (hB b),
    fun c => inv_unit_mod (hC c),
    ?_,
    unitary_conjTranspose hU, ?_⟩
  · -- Inverse cocycle: (sA(a))⁻¹ · (sB(b))⁻¹ · (sC(f.op a b))⁻¹ = (sA(a)·sB(b)·sC(f.op a b))⁻¹ = 1⁻¹ = 1.
    intro a b
    have key := h_cocycle a b
    have hA_ne : sA a ≠ 0 := ne_zero_of_unit_mod (hA a)
    have hB_ne : sB b ≠ 0 := ne_zero_of_unit_mod (hB b)
    have hC_ne : sC (f.op a b) ≠ 0 := ne_zero_of_unit_mod (hC (f.op a b))
    rw [show (sA a)⁻¹ * (sB b)⁻¹ * (sC (f.op a b))⁻¹ =
          (sA a * sB b * sC (f.op a b))⁻¹ from by
      rw [mul_inv, mul_inv]]
    rw [key, inv_one]
  · rw [hΨ]
    exact (combinedGauge_inv U hU sA sB sC
      (fun a => ne_zero_of_unit_mod (hA a))
      (fun b => ne_zero_of_unit_mod (hB b))
      (fun c => ne_zero_of_unit_mod (hC c)) Θ).symm

/-- Transitivity of `feasibleCombinedGaugeOrbit`: composed gauge factors preserve
    the support cocycle (1 · 1 = 1). -/
theorem feasibleCombinedGaugeOrbit_trans {Θ Ψ Φ : HCParams n} {f : BinOp n}
    (h₁ : Ψ ∈ feasibleCombinedGaugeOrbit Θ f)
    (h₂ : Φ ∈ feasibleCombinedGaugeOrbit Ψ f) :
    Φ ∈ feasibleCombinedGaugeOrbit Θ f := by
  obtain ⟨U₁, sA₁, sB₁, sC₁, hA₁, hB₁, hC₁, h_cocycle₁, hU₁, hΨ⟩ := h₁
  obtain ⟨U₂, sA₂, sB₂, sC₂, hA₂, hB₂, hC₂, h_cocycle₂, hU₂, hΦ⟩ := h₂
  refine ⟨U₂ * U₁,
    fun a => sA₂ a * sA₁ a, fun b => sB₂ b * sB₁ b, fun c => sC₂ c * sC₁ c,
    fun a => mul_unit_mod (hA₂ a) (hA₁ a),
    fun b => mul_unit_mod (hB₂ b) (hB₁ b),
    fun c => mul_unit_mod (hC₂ c) (hC₁ c),
    ?_,
    unitary_mul hU₂ hU₁, ?_⟩
  · -- Combined cocycle: (sA₂·sA₁)(a) · (sB₂·sB₁)(b) · (sC₂·sC₁)(f.op a b)
    -- = (sA₂(a)·sB₂(b)·sC₂(f.op a b)) · (sA₁(a)·sB₁(b)·sC₁(f.op a b)) = 1 · 1 = 1.
    intro a b
    rw [show
      sA₂ a * sA₁ a * (sB₂ b * sB₁ b) * (sC₂ (f.op a b) * sC₁ (f.op a b)) =
      (sA₂ a * sB₂ b * sC₂ (f.op a b)) * (sA₁ a * sB₁ b * sC₁ (f.op a b)) from by ring]
    rw [h_cocycle₂ a b, h_cocycle₁ a b, mul_one]
  · rw [hΦ, hΨ]
    exact combinedGauge_mul U₁ U₂ sA₁ sB₁ sC₁ sA₂ sB₂ sC₂ Θ

/-- The feasibility-preserving combined gauge orbit gives an equivalence relation
    on `HCParams n` (parameterised by the BinOp `f`). -/
def feasibleCombinedGaugeSetoid (n : ℕ) [NeZero n] (f : BinOp n) : Setoid (HCParams n) where
  r Θ Ψ := Ψ ∈ feasibleCombinedGaugeOrbit Θ f
  iseqv :=
    ⟨fun Θ => mem_feasibleCombinedGaugeOrbit_self Θ f,
     feasibleCombinedGaugeOrbit_symm,
     feasibleCombinedGaugeOrbit_trans⟩

/-- The quotient of `HCParams n` by the feasibility-preserving combined gauge
    equivalence relation. -/
def FeasibleCombinedGaugeQuotient (n : ℕ) [NeZero n] (f : BinOp n) : Type :=
  Quotient (feasibleCombinedGaugeSetoid n f)

/-! ## Descents to feasibleCombinedGaugeQuotient -/

/-- The `objective` function descends to the feasibility-preserving combined
    gauge quotient. -/
theorem objective_descends_to_feasibleCombinedGaugeQuotient (f : BinOp n) :
    ∀ Θ Ψ : HCParams n, (feasibleCombinedGaugeSetoid n f).r Θ Ψ →
      objective Θ f = objective Ψ f := by
  intro Θ Ψ h
  exact objective_descends_to_combinedGaugeQuotient f Θ Ψ
    (feasibleCombinedGaugeOrbit_subset Θ f h)

/-- `inverseScalePenalty` descends to the feasibility-preserving quotient. -/
theorem inverseScalePenalty_descends_to_feasibleCombinedGaugeQuotient (f : BinOp n) :
    ∀ Θ Ψ : HCParams n, (feasibleCombinedGaugeSetoid n f).r Θ Ψ →
      inverseScalePenalty Θ f = inverseScalePenalty Ψ f := by
  intro Θ Ψ h
  exact inverseScalePenalty_descends_to_combinedGaugeQuotient f Θ Ψ
    (feasibleCombinedGaugeOrbit_subset Θ f h)

/-- `hcNormSq` descends to the feasibility-preserving quotient. -/
theorem hcNormSq_descends_to_feasibleCombinedGaugeQuotient (f : BinOp n) :
    ∀ Θ Ψ : HCParams n, (feasibleCombinedGaugeSetoid n f).r Θ Ψ →
      Tikhonov.hcNormSq Θ = Tikhonov.hcNormSq Ψ := by
  intro Θ Ψ h
  exact hcNormSq_descends_to_combinedGaugeQuotient Θ Ψ
    (feasibleCombinedGaugeOrbit_subset Θ f h)

/-- `kappaTriple` descends to the feasibility-preserving quotient. -/
theorem kappaTriple_descends_to_feasibleCombinedGaugeQuotient (f : BinOp n)
    (a b c : Fin n) :
    ∀ Θ Ψ : HCParams n, (feasibleCombinedGaugeSetoid n f).r Θ Ψ →
      kappaTriple Θ a b c = kappaTriple Ψ a b c := by
  intro Θ Ψ h
  exact kappaTriple_descends_to_combinedGaugeQuotient a b c Θ Ψ
    (feasibleCombinedGaugeOrbit_subset Θ f h)

/-- `Factorizes f` is gauge-invariant on the feasibility-preserving orbit. -/
theorem factorizes_iff_feasibleCombinedGaugeOrbit {Θ Ψ : HCParams n} {f : BinOp n}
    (h : Ψ ∈ feasibleCombinedGaugeOrbit Θ f) :
    Factorizes Θ f ↔ Factorizes Ψ f :=
  ⟨factorizes_of_feasibleCombinedGaugeOrbit f h,
   factorizes_of_feasibleCombinedGaugeOrbit f (feasibleCombinedGaugeOrbit_symm h)⟩

/-- `PerfectCollinearity f` is gauge-invariant on the feasibility-preserving
    orbit (assuming Nondegenerate at any orbit point — gauge-invariant). -/
theorem perfectCollinearity_iff_feasibleCombinedGaugeOrbit {Θ Ψ : HCParams n}
    {f : BinOp n} (h : Ψ ∈ feasibleCombinedGaugeOrbit Θ f)
    (hnd : Nondegenerate Θ) :
    PerfectCollinearity Θ f ↔ PerfectCollinearity Ψ f :=
  ⟨fun hcol => perfectCollinearity_of_combinedGaugeOrbit f
      (feasibleCombinedGaugeOrbit_subset Θ f h) hcol hnd,
   fun hcol => perfectCollinearity_of_combinedGaugeOrbit f
      (feasibleCombinedGaugeOrbit_subset Ψ f (feasibleCombinedGaugeOrbit_symm h))
      hcol (nondegenerate_of_combinedGaugeOrbit Θ Ψ
        (feasibleCombinedGaugeOrbit_subset Θ f h) hnd)⟩

/-- `UnitaryCollinear f` is gauge-invariant on the feasibility-preserving orbit. -/
theorem unitaryCollinear_iff_feasibleCombinedGaugeOrbit {Θ Ψ : HCParams n}
    {f : BinOp n} (h : Ψ ∈ feasibleCombinedGaugeOrbit Θ f) :
    UnitaryCollinear Θ f ↔ UnitaryCollinear Ψ f :=
  ⟨unitaryCollinear_of_feasibleCombinedGaugeOrbit f h,
   unitaryCollinear_of_feasibleCombinedGaugeOrbit f (feasibleCombinedGaugeOrbit_symm h)⟩

/-! ## Lifted functions and predicates on the quotient -/

/-- The objective lifted to the combined gauge quotient. -/
def CombinedGaugeQuotient.objective (f : BinOp n)
    (q : CombinedGaugeQuotient n) : ℂ :=
  q.lift (fun Θ => _root_.objective Θ f)
    (fun Θ Ψ h => objective_descends_to_combinedGaugeQuotient f Θ Ψ h)

/-- `hcNormSq` lifted to the combined gauge quotient. -/
def CombinedGaugeQuotient.hcNormSq (q : CombinedGaugeQuotient n) : ℂ :=
  q.lift Tikhonov.hcNormSq
    (fun Θ Ψ h => hcNormSq_descends_to_combinedGaugeQuotient Θ Ψ h)

/-- `kappaTriple` (at fixed `a b c`) lifted to the combined gauge quotient. -/
def CombinedGaugeQuotient.kappaTriple (a b c : Fin n)
    (q : CombinedGaugeQuotient n) : ℂ :=
  q.lift (fun Θ => _root_.kappaTriple Θ a b c)
    (fun Θ Ψ h => kappaTriple_descends_to_combinedGaugeQuotient a b c Θ Ψ h)

/-- `inverseScalePenalty` lifted to the combined gauge quotient. -/
def CombinedGaugeQuotient.inverseScalePenalty (f : BinOp n)
    (q : CombinedGaugeQuotient n) : ℂ :=
  q.lift (fun Θ => _root_.inverseScalePenalty Θ f)
    (fun Θ Ψ h => inverseScalePenalty_descends_to_combinedGaugeQuotient f Θ Ψ h)

/-- `Nondegenerate` lifted to the combined gauge quotient as a predicate. -/
def CombinedGaugeQuotient.Nondegenerate (q : CombinedGaugeQuotient n) : Prop :=
  q.liftOn _root_.Nondegenerate
    (fun Θ Ψ h => propext (nondegenerate_iff_combinedGaugeOrbit h))

/-- The objective lifted to the feasibility-preserving combined gauge quotient. -/
def FeasibleCombinedGaugeQuotient.objective {f : BinOp n}
    (q : FeasibleCombinedGaugeQuotient n f) : ℂ :=
  q.lift (fun Θ => _root_.objective Θ f)
    (fun Θ Ψ h => objective_descends_to_feasibleCombinedGaugeQuotient f Θ Ψ h)

/-- `Factorizes f` lifted to the feasibility-preserving quotient. -/
def FeasibleCombinedGaugeQuotient.Factorizes {f : BinOp n}
    (q : FeasibleCombinedGaugeQuotient n f) : Prop :=
  q.liftOn (fun Θ => _root_.Factorizes Θ f)
    (fun Θ Ψ h => propext (factorizes_iff_feasibleCombinedGaugeOrbit h))

/-- `UnitaryCollinear f` lifted to the feasibility-preserving quotient. -/
def FeasibleCombinedGaugeQuotient.UnitaryCollinear {f : BinOp n}
    (q : FeasibleCombinedGaugeQuotient n f) : Prop :=
  q.liftOn (fun Θ => _root_.UnitaryCollinear Θ f)
    (fun Θ Ψ h => propext (unitaryCollinear_iff_feasibleCombinedGaugeOrbit h))

/-! ## kappa=1 hypothesis gauge invariance -/

/-- "κ=1 on support" is preserved on the combined gauge orbit. -/
theorem kappa_one_of_combinedGaugeOrbit {Θ Ψ : HCParams n} (f : BinOp n)
    (h : Ψ ∈ combinedGaugeOrbit Θ)
    (hκ : ∀ a b : Fin n, kappaTriple Θ a b (f.op a b) = 1) :
    ∀ a b : Fin n, kappaTriple Ψ a b (f.op a b) = 1 := by
  intro a b
  rw [kappaTriple_constant_on_combinedGaugeOrbit Θ Ψ h]
  exact hκ a b

/-- "κ=1 on support" is gauge-invariant — iff form. -/
theorem kappa_one_iff_combinedGaugeOrbit {Θ Ψ : HCParams n} (f : BinOp n)
    (h : Ψ ∈ combinedGaugeOrbit Θ) :
    (∀ a b : Fin n, kappaTriple Θ a b (f.op a b) = 1) ↔
    (∀ a b : Fin n, kappaTriple Ψ a b (f.op a b) = 1) :=
  ⟨kappa_one_of_combinedGaugeOrbit f h,
   kappa_one_of_combinedGaugeOrbit f (combinedGaugeOrbit_symm h)⟩

/-- The "PCFN + κ=1" hypothesis is preserved on the feasibility-preserving orbit. -/
theorem kappa_one_PCFN_of_feasibleCombinedGaugeOrbit {Θ Ψ : HCParams n} (f : BinOp n)
    (h : Ψ ∈ feasibleCombinedGaugeOrbit Θ f)
    (hcol : PerfectCollinearity Θ f) (hfeas : Factorizes Θ f) (hnd : Nondegenerate Θ)
    (hκ : ∀ a b : Fin n, kappaTriple Θ a b (f.op a b) = 1) :
    PerfectCollinearity Ψ f ∧ Factorizes Ψ f ∧ Nondegenerate Ψ ∧
    (∀ a b : Fin n, kappaTriple Ψ a b (f.op a b) = 1) := by
  obtain ⟨hcol', hfeas', hnd'⟩ := PCFN_of_feasibleCombinedGaugeOrbit f h hcol hfeas hnd
  refine ⟨hcol', hfeas', hnd', ?_⟩
  exact kappa_one_of_combinedGaugeOrbit f
    (feasibleCombinedGaugeOrbit_subset Θ f h) hκ

/-! ## Simp lemmas for lifted quotient functions -/

@[simp] theorem CombinedGaugeQuotient.objective_mk (f : BinOp n) (Θ : HCParams n) :
    CombinedGaugeQuotient.objective f (Quotient.mk (combinedGaugeSetoid n) Θ) =
    _root_.objective Θ f := rfl

@[simp] theorem CombinedGaugeQuotient.hcNormSq_mk (Θ : HCParams n) :
    CombinedGaugeQuotient.hcNormSq (Quotient.mk (combinedGaugeSetoid n) Θ) =
    Tikhonov.hcNormSq Θ := rfl

@[simp] theorem CombinedGaugeQuotient.kappaTriple_mk (a b c : Fin n) (Θ : HCParams n) :
    CombinedGaugeQuotient.kappaTriple a b c (Quotient.mk (combinedGaugeSetoid n) Θ) =
    _root_.kappaTriple Θ a b c := rfl

@[simp] theorem CombinedGaugeQuotient.inverseScalePenalty_mk (f : BinOp n) (Θ : HCParams n) :
    CombinedGaugeQuotient.inverseScalePenalty f (Quotient.mk (combinedGaugeSetoid n) Θ) =
    _root_.inverseScalePenalty Θ f := rfl

@[simp] theorem CombinedGaugeQuotient.Nondegenerate_mk (Θ : HCParams n) :
    CombinedGaugeQuotient.Nondegenerate (Quotient.mk (combinedGaugeSetoid n) Θ) =
    _root_.Nondegenerate Θ := rfl

@[simp] theorem FeasibleCombinedGaugeQuotient.objective_mk (f : BinOp n) (Θ : HCParams n) :
    FeasibleCombinedGaugeQuotient.objective
      (Quotient.mk (feasibleCombinedGaugeSetoid n f) Θ : FeasibleCombinedGaugeQuotient n f) =
    _root_.objective Θ f := rfl

@[simp] theorem FeasibleCombinedGaugeQuotient.Factorizes_mk (f : BinOp n) (Θ : HCParams n) :
    FeasibleCombinedGaugeQuotient.Factorizes
      (Quotient.mk (feasibleCombinedGaugeSetoid n f) Θ : FeasibleCombinedGaugeQuotient n f) =
    _root_.Factorizes Θ f := rfl

@[simp] theorem FeasibleCombinedGaugeQuotient.UnitaryCollinear_mk (f : BinOp n)
    (Θ : HCParams n) :
    FeasibleCombinedGaugeQuotient.UnitaryCollinear
      (Quotient.mk (feasibleCombinedGaugeSetoid n f) Θ : FeasibleCombinedGaugeQuotient n f) =
    _root_.UnitaryCollinear Θ f := rfl

/-! ## Additional lifts to FeasibleCombinedGaugeQuotient -/

/-- `inverseScalePenalty` lifted to the feasibility-preserving quotient. -/
def FeasibleCombinedGaugeQuotient.inverseScalePenalty {f : BinOp n}
    (q : FeasibleCombinedGaugeQuotient n f) : ℂ :=
  q.lift (fun Θ => _root_.inverseScalePenalty Θ f)
    (fun Θ Ψ h => inverseScalePenalty_descends_to_feasibleCombinedGaugeQuotient f Θ Ψ h)

/-- `hcNormSq` lifted to the feasibility-preserving quotient. -/
def FeasibleCombinedGaugeQuotient.hcNormSq {f : BinOp n}
    (q : FeasibleCombinedGaugeQuotient n f) : ℂ :=
  q.lift Tikhonov.hcNormSq
    (fun Θ Ψ h => hcNormSq_descends_to_feasibleCombinedGaugeQuotient f Θ Ψ h)

/-- `kappaTriple` lifted to the feasibility-preserving quotient. -/
def FeasibleCombinedGaugeQuotient.kappaTriple {f : BinOp n} (a b c : Fin n)
    (q : FeasibleCombinedGaugeQuotient n f) : ℂ :=
  q.lift (fun Θ => _root_.kappaTriple Θ a b c)
    (fun Θ Ψ h => kappaTriple_descends_to_feasibleCombinedGaugeQuotient f a b c Θ Ψ h)

/-- `Nondegenerate` lifted to the feasibility-preserving quotient. Since
    Nondegenerate is invariant on `combinedGaugeOrbit` ⊇ `feasibleCombinedGaugeOrbit`,
    it descends here too. -/
def FeasibleCombinedGaugeQuotient.Nondegenerate {f : BinOp n}
    (q : FeasibleCombinedGaugeQuotient n f) : Prop :=
  q.liftOn _root_.Nondegenerate
    (fun Θ Ψ h => propext (nondegenerate_iff_combinedGaugeOrbit
      (feasibleCombinedGaugeOrbit_subset Θ f h)))

@[simp] theorem FeasibleCombinedGaugeQuotient.inverseScalePenalty_mk (f : BinOp n)
    (Θ : HCParams n) :
    FeasibleCombinedGaugeQuotient.inverseScalePenalty
      (Quotient.mk (feasibleCombinedGaugeSetoid n f) Θ : FeasibleCombinedGaugeQuotient n f) =
    _root_.inverseScalePenalty Θ f := rfl

@[simp] theorem FeasibleCombinedGaugeQuotient.hcNormSq_mk (f : BinOp n) (Θ : HCParams n) :
    FeasibleCombinedGaugeQuotient.hcNormSq
      (Quotient.mk (feasibleCombinedGaugeSetoid n f) Θ : FeasibleCombinedGaugeQuotient n f) =
    Tikhonov.hcNormSq Θ := rfl

@[simp] theorem FeasibleCombinedGaugeQuotient.kappaTriple_mk (f : BinOp n)
    (a b c : Fin n) (Θ : HCParams n) :
    FeasibleCombinedGaugeQuotient.kappaTriple a b c
      (Quotient.mk (feasibleCombinedGaugeSetoid n f) Θ : FeasibleCombinedGaugeQuotient n f) =
    _root_.kappaTriple Θ a b c := rfl

@[simp] theorem FeasibleCombinedGaugeQuotient.Nondegenerate_mk (f : BinOp n)
    (Θ : HCParams n) :
    FeasibleCombinedGaugeQuotient.Nondegenerate
      (Quotient.mk (feasibleCombinedGaugeSetoid n f) Θ : FeasibleCombinedGaugeQuotient n f) =
    _root_.Nondegenerate Θ := rfl

/-! ## Subset relations: unitaryGaugeOrbit and uniformScale ⊆ combinedGaugeOrbit -/

/-- `unitaryConjAction U Θ` is a member of the combined gauge orbit (use trivial
    per-slot factors). -/
theorem unitaryConjAction_mem_combinedGaugeOrbit
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U * U.conjTranspose = 1) (Θ : HCParams n) :
    unitaryConjAction U Θ ∈ combinedGaugeOrbit Θ := by
  refine ⟨U, fun _ => 1, fun _ => 1, fun _ => 1, ?_, ?_, ?_, hU, ?_⟩
  · intro a; rw [map_one]; ring
  · intro b; rw [map_one]; ring
  · intro c; rw [map_one]; ring
  · unfold combinedGauge
    rw [gaugeAction_one]

/-- The unitary gauge orbit is a subset of the combined gauge orbit. -/
theorem unitaryGaugeOrbit_subset_combinedGaugeOrbit (Θ : HCParams n) :
    unitaryGaugeOrbit Θ ⊆ combinedGaugeOrbit Θ := by
  intro Ψ ⟨U, hU, hΨ⟩
  rw [hΨ]
  exact unitaryConjAction_mem_combinedGaugeOrbit U hU Θ

/-- `uniformScale t Θ` is a member of the combined gauge orbit when `|t|² = 1`
    (e.g. `t` is a cube root of unity). -/
theorem uniformScale_mem_combinedGaugeOrbit_of_unit_mod
    (t : ℂ) (ht : t * starRingEnd ℂ t = 1) (Θ : HCParams n) :
    uniformScale t Θ ∈ combinedGaugeOrbit Θ := by
  refine ⟨1, fun _ => t, fun _ => t, fun _ => t, ?_, ?_, ?_, ?_, ?_⟩
  · intro _; exact ht
  · intro _; exact ht
  · intro _; exact ht
  · simp
  · show uniformScale t Θ = unitaryConjAction 1 (gaugeAction _ _ _ Θ)
    rw [unitaryConjAction_one]
    rfl

/-- `uniformScale t Θ` is in the combined gauge orbit when `t³ = 1`. -/
theorem uniformScale_cubeRoot_mem_combinedGaugeOrbit (t : ℂ) (ht : t ^ 3 = 1) (Θ : HCParams n) :
    uniformScale t Θ ∈ combinedGaugeOrbit Θ :=
  uniformScale_mem_combinedGaugeOrbit_of_unit_mod t (cubeRoot_norm_one t ht) Θ

/-- `unitaryConjAction U Θ` is in the feasibility-preserving orbit when `Factorizes Θ f`
    holds (since unitary conjugation preserves Factorizes). -/
theorem unitaryConjAction_mem_feasibleCombinedGaugeOrbit
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U * U.conjTranspose = 1) (Θ : HCParams n)
    (f : BinOp n) :
    unitaryConjAction U Θ ∈ feasibleCombinedGaugeOrbit Θ f := by
  refine ⟨U, fun _ => 1, fun _ => 1, fun _ => 1, ?_, ?_, ?_, ?_, hU, ?_⟩
  · intro a; rw [map_one]; ring
  · intro b; rw [map_one]; ring
  · intro c; rw [map_one]; ring
  · intro a b; ring
  · unfold combinedGauge
    rw [gaugeAction_one]

/-- The unitary gauge orbit is a subset of the feasibility-preserving combined gauge
    orbit. -/
theorem unitaryGaugeOrbit_subset_feasibleCombinedGaugeOrbit (Θ : HCParams n) (f : BinOp n) :
    unitaryGaugeOrbit Θ ⊆ feasibleCombinedGaugeOrbit Θ f := by
  intro Ψ ⟨U, hU, hΨ⟩
  rw [hΨ]
  exact unitaryConjAction_mem_feasibleCombinedGaugeOrbit U hU Θ f

/-- `uniformScale t Θ` is in the feasibility-preserving orbit when `t³ = 1`
    (cube-root scaling preserves the cocycle: `t · t · t = t³ = 1`). -/
theorem uniformScale_cubeRoot_mem_feasibleCombinedGaugeOrbit
    (t : ℂ) (ht : t ^ 3 = 1) (Θ : HCParams n) (f : BinOp n) :
    uniformScale t Θ ∈ feasibleCombinedGaugeOrbit Θ f := by
  have h_norm : t * starRingEnd ℂ t = 1 := cubeRoot_norm_one t ht
  refine ⟨1, fun _ => t, fun _ => t, fun _ => t, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _; exact h_norm
  · intro _; exact h_norm
  · intro _; exact h_norm
  · intro a b
    -- Cocycle: t · t · t = t³ = 1
    have : t * t * t = t ^ 3 := by ring
    rw [this, ht]
  · simp
  · show uniformScale t Θ = unitaryConjAction 1 (gaugeAction _ _ _ Θ)
    rw [unitaryConjAction_one]
    rfl

/-- `unitaryConjAction U (uniformScale t Θ)` is in the feasibility-preserving
    orbit when `U` is unitary and `t³ = 1`. Combines the previous two
    inclusions via `combinedGauge_mul`. -/
theorem unitaryConj_uniformScale_cubeRoot_mem_feasibleCombinedGaugeOrbit
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U * U.conjTranspose = 1)
    (t : ℂ) (ht : t ^ 3 = 1) (Θ : HCParams n) (f : BinOp n) :
    unitaryConjAction U (uniformScale t Θ) ∈ feasibleCombinedGaugeOrbit Θ f := by
  have h_norm : t * starRingEnd ℂ t = 1 := cubeRoot_norm_one t ht
  refine ⟨U, fun _ => t, fun _ => t, fun _ => t, ?_, ?_, ?_, ?_, hU, ?_⟩
  · intro _; exact h_norm
  · intro _; exact h_norm
  · intro _; exact h_norm
  · intro a b
    have : t * t * t = t ^ 3 := by ring
    rw [this, ht]
  · show unitaryConjAction U (uniformScale t Θ) =
        unitaryConjAction U (gaugeAction _ _ _ Θ)
    rfl

/-- `uniformScale t (unitaryConjAction U Θ)` is in the feasibility-preserving orbit
    (using commutativity of the actions). -/
theorem uniformScale_unitaryConj_cubeRoot_mem_feasibleCombinedGaugeOrbit
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U * U.conjTranspose = 1)
    (t : ℂ) (ht : t ^ 3 = 1) (Θ : HCParams n) (f : BinOp n) :
    uniformScale t (unitaryConjAction U Θ) ∈ feasibleCombinedGaugeOrbit Θ f := by
  rw [show uniformScale t (unitaryConjAction U Θ) =
        unitaryConjAction U (uniformScale t Θ) from by
    show gaugeAction _ _ _ (unitaryConjAction U Θ) =
         unitaryConjAction U (gaugeAction _ _ _ Θ)
    rw [← gaugeAction_unitaryConjAction_comm]]
  exact unitaryConj_uniformScale_cubeRoot_mem_feasibleCombinedGaugeOrbit U hU t ht Θ f

/-! ## Natural map between quotients -/

/-- The natural map from the feasibility-preserving combined gauge quotient to the
    full combined gauge quotient. The feasibility-preserving relation is finer
    (more pairs are inequivalent), so equivalence classes map injectively. -/
def feasibleToCombinedGaugeQuotient (f : BinOp n) :
    FeasibleCombinedGaugeQuotient n f → CombinedGaugeQuotient n :=
  Quotient.map id (fun _ _ h => feasibleCombinedGaugeOrbit_subset _ f h)

@[simp] theorem feasibleToCombinedGaugeQuotient_mk (f : BinOp n) (Θ : HCParams n) :
    feasibleToCombinedGaugeQuotient f
      (Quotient.mk (feasibleCombinedGaugeSetoid n f) Θ) =
    Quotient.mk (combinedGaugeSetoid n) Θ := rfl

/-- The objective on the feasible quotient equals the objective on the natural
    image in the combined quotient. -/
theorem objective_feasibleToCombinedGaugeQuotient_eq (f : BinOp n)
    (q : FeasibleCombinedGaugeQuotient n f) :
    FeasibleCombinedGaugeQuotient.objective q =
    CombinedGaugeQuotient.objective f (feasibleToCombinedGaugeQuotient f q) := by
  induction q using Quotient.ind with
  | _ Θ => rfl

/-- The hcNormSq on the feasible quotient equals it on the natural image. -/
theorem hcNormSq_feasibleToCombinedGaugeQuotient_eq (f : BinOp n)
    (q : FeasibleCombinedGaugeQuotient n f) :
    FeasibleCombinedGaugeQuotient.hcNormSq q =
    CombinedGaugeQuotient.hcNormSq (feasibleToCombinedGaugeQuotient f q) := by
  induction q using Quotient.ind with
  | _ Θ => rfl

/-- The natural quotient map is surjective: every combined gauge equivalence class
    has a representative that is also a feasible gauge equivalence class. -/
theorem feasibleToCombinedGaugeQuotient_surjective (f : BinOp n) :
    Function.Surjective (feasibleToCombinedGaugeQuotient f) := by
  intro q
  induction q using Quotient.ind with
  | _ Θ =>
    refine ⟨Quotient.mk (feasibleCombinedGaugeSetoid n f) Θ, ?_⟩
    rfl

/-- The kappaTriple on the feasible quotient equals it on the natural image. -/
theorem kappaTriple_feasibleToCombinedGaugeQuotient_eq (f : BinOp n) (a b c : Fin n)
    (q : FeasibleCombinedGaugeQuotient n f) :
    FeasibleCombinedGaugeQuotient.kappaTriple a b c q =
    CombinedGaugeQuotient.kappaTriple a b c (feasibleToCombinedGaugeQuotient f q) := by
  induction q using Quotient.ind with
  | _ Θ => rfl

/-- The inverseScalePenalty on the feasible quotient equals it on the natural image. -/
theorem inverseScalePenalty_feasibleToCombinedGaugeQuotient_eq (f : BinOp n)
    (q : FeasibleCombinedGaugeQuotient n f) :
    FeasibleCombinedGaugeQuotient.inverseScalePenalty q =
    CombinedGaugeQuotient.inverseScalePenalty f (feasibleToCombinedGaugeQuotient f q) := by
  induction q using Quotient.ind with
  | _ Θ => rfl

/-- The Nondegenerate predicate on the feasible quotient equals it on the natural
    image. -/
theorem Nondegenerate_feasibleToCombinedGaugeQuotient_eq (f : BinOp n)
    (q : FeasibleCombinedGaugeQuotient n f) :
    FeasibleCombinedGaugeQuotient.Nondegenerate q =
    CombinedGaugeQuotient.Nondegenerate (feasibleToCombinedGaugeQuotient f q) := by
  induction q using Quotient.ind with
  | _ Θ => rfl

/-! ## Continuity of gauge actions in Θ -/

/-- For fixed per-slot factors, `gaugeAction sA sB sC` is continuous on `HCParams n`
    (it is linear in `Θ`). -/
theorem continuous_gaugeAction (sA sB sC : Fin n → ℂ) :
    Continuous (gaugeAction sA sB sC : HCParams n → HCParams n) := by
  apply continuous_induced_rng.mpr
  refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_)
  · apply continuous_pi
    intro a
    exact (HCParams.continuous_A a).const_smul (sA a)
  · apply continuous_pi
    intro b
    exact (HCParams.continuous_B b).const_smul (sB b)
  · apply continuous_pi
    intro c
    exact (HCParams.continuous_C c).const_smul (sC c)

/-- For fixed unitary `U`, `unitaryConjAction U` is continuous on `HCParams n`
    (it is linear in `Θ`). -/
theorem continuous_unitaryConjAction (U : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (unitaryConjAction U : HCParams n → HCParams n) := by
  apply continuous_induced_rng.mpr
  refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_)
  · apply continuous_pi
    intro a
    exact (continuous_const.matrix_mul (HCParams.continuous_A a)).matrix_mul continuous_const
  · apply continuous_pi
    intro b
    exact (continuous_const.matrix_mul (HCParams.continuous_B b)).matrix_mul continuous_const
  · apply continuous_pi
    intro c
    exact (continuous_const.matrix_mul (HCParams.continuous_C c)).matrix_mul continuous_const

/-- For fixed unitary `U` and per-slot factors, `combinedGauge U sA sB sC` is
    continuous on `HCParams n`. -/
theorem continuous_combinedGauge
    (U : Matrix (Fin n) (Fin n) ℂ) (sA sB sC : Fin n → ℂ) :
    Continuous (combinedGauge U sA sB sC : HCParams n → HCParams n) :=
  (continuous_unitaryConjAction U).comp (continuous_gaugeAction sA sB sC)

/-- For fixed `t`, `uniformScale t` is continuous on `HCParams n`. -/
theorem continuous_uniformScale (t : ℂ) :
    Continuous (uniformScale t : HCParams n → HCParams n) :=
  continuous_gaugeAction _ _ _

/-- For fixed `Θ`, the map `U ↦ unitaryConjAction U Θ` is continuous (linear in U
    via matrix multiplication and conjugate transpose). -/
theorem continuous_unitaryConjAction_in_U (Θ : HCParams n) :
    Continuous (fun U : Matrix (Fin n) (Fin n) ℂ => unitaryConjAction U Θ) := by
  apply continuous_induced_rng.mpr
  refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_)
  · apply continuous_pi
    intro a
    -- U ↦ U * Θ.A a * Uᴴ
    exact (continuous_id.matrix_mul continuous_const).matrix_mul
      continuous_id.matrix_conjTranspose
  · apply continuous_pi
    intro b
    exact (continuous_id.matrix_mul continuous_const).matrix_mul
      continuous_id.matrix_conjTranspose
  · apply continuous_pi
    intro c
    exact (continuous_id.matrix_mul continuous_const).matrix_mul
      continuous_id.matrix_conjTranspose

/-- For fixed `Θ`, the map `t ↦ uniformScale t Θ` is continuous in `t`. -/
theorem continuous_uniformScale_in_t (Θ : HCParams n) :
    Continuous (fun t : ℂ => uniformScale t Θ) := by
  apply continuous_induced_rng.mpr
  refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_)
  · apply continuous_pi
    intro a
    exact continuous_id.smul continuous_const
  · apply continuous_pi
    intro b
    exact continuous_id.smul continuous_const
  · apply continuous_pi
    intro c
    exact continuous_id.smul continuous_const

/-- Joint continuity of `unitaryConjAction` in `(U, Θ)`. -/
theorem continuous_unitaryConjAction_jointly :
    Continuous (fun p : Matrix (Fin n) (Fin n) ℂ × HCParams n =>
      unitaryConjAction p.1 p.2) := by
  apply continuous_induced_rng.mpr
  refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_)
  · apply continuous_pi
    intro a
    -- (U, Θ) ↦ U * Θ.A a * Uᴴ
    refine (continuous_fst.matrix_mul ?_).matrix_mul continuous_fst.matrix_conjTranspose
    exact (HCParams.continuous_A a).comp continuous_snd
  · apply continuous_pi
    intro b
    refine (continuous_fst.matrix_mul ?_).matrix_mul continuous_fst.matrix_conjTranspose
    exact (HCParams.continuous_B b).comp continuous_snd
  · apply continuous_pi
    intro c
    refine (continuous_fst.matrix_mul ?_).matrix_mul continuous_fst.matrix_conjTranspose
    exact (HCParams.continuous_C c).comp continuous_snd

/-- Joint continuity of `uniformScale` in `(t, Θ)`. -/
theorem continuous_uniformScale_jointly :
    Continuous (fun p : ℂ × HCParams n => uniformScale p.1 p.2) := by
  apply continuous_induced_rng.mpr
  refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_)
  · apply continuous_pi
    intro a
    -- (t, Θ) ↦ t • Θ.A a
    exact continuous_fst.smul ((HCParams.continuous_A a).comp continuous_snd)
  · apply continuous_pi
    intro b
    exact continuous_fst.smul ((HCParams.continuous_B b).comp continuous_snd)
  · apply continuous_pi
    intro c
    exact continuous_fst.smul ((HCParams.continuous_C c).comp continuous_snd)

/-! ## Per-slot only inclusions in gauge orbits -/

/-- Pure per-slot gauge action with unit-modulus factors is in the combined orbit
    (take `U = 1`). -/
theorem gaugeAction_unit_mem_combinedGaugeOrbit
    (sA sB sC : Fin n → ℂ) (Θ : HCParams n)
    (hA : ∀ a, sA a * starRingEnd ℂ (sA a) = 1)
    (hB : ∀ b, sB b * starRingEnd ℂ (sB b) = 1)
    (hC : ∀ c, sC c * starRingEnd ℂ (sC c) = 1) :
    gaugeAction sA sB sC Θ ∈ combinedGaugeOrbit Θ := by
  refine ⟨1, sA, sB, sC, hA, hB, hC, ?_, ?_⟩
  · simp
  · show gaugeAction sA sB sC Θ = unitaryConjAction 1 (gaugeAction sA sB sC Θ)
    rw [unitaryConjAction_one]

/-- Pure per-slot gauge action with unit-modulus + cocycle is in the feasibility-
    preserving orbit (take `U = 1`). -/
theorem gaugeAction_unit_cocycle_mem_feasibleCombinedGaugeOrbit
    (sA sB sC : Fin n → ℂ) (Θ : HCParams n) (f : BinOp n)
    (hA : ∀ a, sA a * starRingEnd ℂ (sA a) = 1)
    (hB : ∀ b, sB b * starRingEnd ℂ (sB b) = 1)
    (hC : ∀ c, sC c * starRingEnd ℂ (sC c) = 1)
    (h_cocycle : ∀ a b, sA a * sB b * sC (f.op a b) = 1) :
    gaugeAction sA sB sC Θ ∈ feasibleCombinedGaugeOrbit Θ f := by
  refine ⟨1, sA, sB, sC, hA, hB, hC, h_cocycle, ?_, ?_⟩
  · simp
  · show gaugeAction sA sB sC Θ = unitaryConjAction 1 (gaugeAction sA sB sC Θ)
    rw [unitaryConjAction_one]

/-- The pure per-slot unit-modulus gauge orbit (without unitary part) is a subset
    of the combined gauge orbit. -/
theorem gaugeAction_unit_orbit_subset_combinedGaugeOrbit (Θ : HCParams n) :
    { Ψ | ∃ sA sB sC : Fin n → ℂ,
          (∀ a, sA a * starRingEnd ℂ (sA a) = 1) ∧
          (∀ b, sB b * starRingEnd ℂ (sB b) = 1) ∧
          (∀ c, sC c * starRingEnd ℂ (sC c) = 1) ∧
          Ψ = gaugeAction sA sB sC Θ } ⊆ combinedGaugeOrbit Θ := by
  intro Ψ ⟨sA, sB, sC, hA, hB, hC, hΨ⟩
  rw [hΨ]
  exact gaugeAction_unit_mem_combinedGaugeOrbit sA sB sC Θ hA hB hC

/-! ## Inequality preservation on gauge orbits -/

/-- If `Ψ ∈ combinedGaugeOrbit Θ`, then `(objective Θ f).re ≤ M ↔ (objective Ψ f).re ≤ M`. -/
theorem objective_re_le_iff_combinedGaugeOrbit {Θ Ψ : HCParams n}
    (h : Ψ ∈ combinedGaugeOrbit Θ) (f : BinOp n) (M : ℝ) :
    (objective Θ f).re ≤ M ↔ (objective Ψ f).re ≤ M := by
  rw [objective_constant_on_combinedGaugeOrbit Θ Ψ f h]

/-- If `Ψ ∈ combinedGaugeOrbit Θ`, then `M ≤ (objective Θ f).re ↔ M ≤ (objective Ψ f).re`. -/
theorem le_objective_re_iff_combinedGaugeOrbit {Θ Ψ : HCParams n}
    (h : Ψ ∈ combinedGaugeOrbit Θ) (f : BinOp n) (M : ℝ) :
    M ≤ (objective Θ f).re ↔ M ≤ (objective Ψ f).re := by
  rw [objective_constant_on_combinedGaugeOrbit Θ Ψ f h]

/-- If `Ψ ∈ combinedGaugeOrbit Θ`, then `(hcNormSq Θ).re ≤ M ↔ (hcNormSq Ψ).re ≤ M`. -/
theorem hcNormSq_re_le_iff_combinedGaugeOrbit {Θ Ψ : HCParams n}
    (h : Ψ ∈ combinedGaugeOrbit Θ) (M : ℝ) :
    (Tikhonov.hcNormSq Θ).re ≤ M ↔ (Tikhonov.hcNormSq Ψ).re ≤ M := by
  rw [hcNormSq_constant_on_combinedGaugeOrbit Θ Ψ h]

/-- AM-GM lower bound is gauge-invariant: if `Θ` is feasible/PCFN with
    `(inverseScalePenalty Θ f).re ≥ 3n²`, the same holds for any orbit member. -/
theorem inverseScalePenalty_re_lower_bound_on_combinedGaugeOrbit
    {Θ Ψ : HCParams n} (h : Ψ ∈ combinedGaugeOrbit Θ) (f : BinOp n) (M : ℝ)
    (hΘ : M ≤ (inverseScalePenalty Θ f).re) :
    M ≤ (inverseScalePenalty Ψ f).re := by
  rw [inverseScalePenalty_constant_on_combinedGaugeOrbit Θ Ψ f h]
  exact hΘ

/-! ## AM-GM lower bound on the gauge quotient -/

/-- AM-GM lower bound at the level of the feasibility-preserving gauge quotient:
    for a UnitaryCollinear factorisation, the (lifted) inverseScalePenalty's real part
    is at least `3n²`. -/
theorem amgm_lower_bound_feasibleQuotient {f : BinOp n} (hq : _root_.IsQuasigroup f)
    (q : FeasibleCombinedGaugeQuotient n f)
    (huc : FeasibleCombinedGaugeQuotient.UnitaryCollinear q) :
    3 * (n : ℝ) ^ 2 ≤ (FeasibleCombinedGaugeQuotient.inverseScalePenalty q).re := by
  induction q using Quotient.ind with
  | _ Θ =>
    -- Unfold via simp lemmas
    show 3 * (n : ℝ) ^ 2 ≤ (_root_.inverseScalePenalty Θ f).re
    have huc' : _root_.UnitaryCollinear Θ f := huc
    -- Recover Nondegenerate from unitarity of slices.
    have hnd : Nondegenerate Θ := {
      A_pos := fun a => by rw [frobNormSq_unitary_eq_one _ (huc'.unitaryA a)]; exact one_ne_zero,
      B_pos := fun b => by rw [frobNormSq_unitary_eq_one _ (huc'.unitaryB b)]; exact one_ne_zero,
      C_pos := fun c => by rw [frobNormSq_unitary_eq_one _ (huc'.unitaryC c)]; exact one_ne_zero }
    exact amgm_lower_bound Θ f hq hnd huc'.collinear huc'.feasible

/-! ## Gauge actions on the zero element -/

/-- The zero `HCParams` is fixed under any per-slot gauge action. -/
@[simp] theorem gaugeAction_zero (sA sB sC : Fin n → ℂ) :
    gaugeAction sA sB sC (0 : HCParams n) = 0 := by
  unfold gaugeAction
  -- Goal: ⟨fun a => sA a • (0 : HCParams n).A a, ...⟩ = 0
  -- Use that (0 : HCParams n) = HCParams.mk (fun _ => 0) (fun _ => 0) (fun _ => 0)
  have hzero : (0 : HCParams n) = ⟨fun _ => 0, fun _ => 0, fun _ => 0⟩ := rfl
  rw [hzero]
  simp [smul_zero]

/-- The zero `HCParams` is fixed under unitary conjugation. -/
@[simp] theorem unitaryConjAction_zero (U : Matrix (Fin n) (Fin n) ℂ) :
    unitaryConjAction U (0 : HCParams n) = 0 := by
  unfold unitaryConjAction
  have hzero : (0 : HCParams n) = ⟨fun _ => 0, fun _ => 0, fun _ => 0⟩ := rfl
  rw [hzero]
  simp [Matrix.zero_mul, Matrix.mul_zero]

/-- The zero `HCParams` is fixed under combined gauge action. -/
@[simp] theorem combinedGauge_zero (U : Matrix (Fin n) (Fin n) ℂ) (sA sB sC : Fin n → ℂ) :
    combinedGauge U sA sB sC (0 : HCParams n) = 0 := by
  unfold combinedGauge
  rw [gaugeAction_zero, unitaryConjAction_zero]

/-- The zero `HCParams` is fixed under uniform scaling. -/
@[simp] theorem uniformScale_zero (t : ℂ) :
    uniformScale t (0 : HCParams n) = 0 :=
  gaugeAction_zero _ _ _

/-! ## Linearity of gauge actions -/

/-- Helper: addition on `HCParams` is componentwise. -/
private theorem HCParams_add_A (Θ Φ : HCParams n) (a : Fin n) :
    (Θ + Φ).A a = Θ.A a + Φ.A a := rfl

private theorem HCParams_add_B (Θ Φ : HCParams n) (b : Fin n) :
    (Θ + Φ).B b = Θ.B b + Φ.B b := rfl

private theorem HCParams_add_C (Θ Φ : HCParams n) (c : Fin n) :
    (Θ + Φ).C c = Θ.C c + Φ.C c := rfl

private theorem HCParams_smul_A (c : ℂ) (Θ : HCParams n) (a : Fin n) :
    (c • Θ).A a = c • Θ.A a := rfl

private theorem HCParams_smul_B (c : ℂ) (Θ : HCParams n) (b : Fin n) :
    (c • Θ).B b = c • Θ.B b := rfl

private theorem HCParams_smul_C (c : ℂ) (Θ : HCParams n) (c' : Fin n) :
    (c • Θ).C c' = c • Θ.C c' := rfl

/-- A and B and C agree pointwise implies HCParams equality. -/
private theorem HCParams_eq_of_components {Θ Φ : HCParams n}
    (hA : ∀ a, Θ.A a = Φ.A a) (hB : ∀ b, Θ.B b = Φ.B b) (hC : ∀ c, Θ.C c = Φ.C c) :
    Θ = Φ := by
  cases Θ; cases Φ
  congr 1 <;> [funext a; funext b; funext c]
  · exact hA a
  · exact hB b
  · exact hC c

/-- Per-slot gauge action is additive in `Θ`. -/
theorem gaugeAction_add (sA sB sC : Fin n → ℂ) (Θ Φ : HCParams n) :
    gaugeAction sA sB sC (Θ + Φ) =
    gaugeAction sA sB sC Θ + gaugeAction sA sB sC Φ := by
  apply HCParams_eq_of_components
  · intro a
    show sA a • (Θ + Φ).A a = sA a • Θ.A a + sA a • Φ.A a
    rw [HCParams_add_A]
    ext i j
    simp [Matrix.smul_apply, Matrix.add_apply, mul_add]
  · intro b
    show sB b • (Θ + Φ).B b = sB b • Θ.B b + sB b • Φ.B b
    rw [HCParams_add_B]
    ext i j
    simp [Matrix.smul_apply, Matrix.add_apply, mul_add]
  · intro c
    show sC c • (Θ + Φ).C c = sC c • Θ.C c + sC c • Φ.C c
    rw [HCParams_add_C]
    ext i j
    simp [Matrix.smul_apply, Matrix.add_apply, mul_add]

/-- Per-slot gauge action is `ℂ`-linear in `Θ`. -/
theorem gaugeAction_smul (sA sB sC : Fin n → ℂ) (c : ℂ) (Θ : HCParams n) :
    gaugeAction sA sB sC (c • Θ) = c • gaugeAction sA sB sC Θ := by
  apply HCParams_eq_of_components
  · intro a
    show sA a • (c • Θ).A a = c • (sA a • Θ.A a)
    rw [HCParams_smul_A]
    ext i j
    simp [Matrix.smul_apply, mul_left_comm]
  · intro b
    show sB b • (c • Θ).B b = c • (sB b • Θ.B b)
    rw [HCParams_smul_B]
    ext i j
    simp [Matrix.smul_apply, mul_left_comm]
  · intro c'
    show sC c' • (c • Θ).C c' = c • (sC c' • Θ.C c')
    rw [HCParams_smul_C]
    ext i j
    simp [Matrix.smul_apply, mul_left_comm]

/-- Unitary conjugation is additive in `Θ`. -/
theorem unitaryConjAction_add (U : Matrix (Fin n) (Fin n) ℂ) (Θ Φ : HCParams n) :
    unitaryConjAction U (Θ + Φ) =
    unitaryConjAction U Θ + unitaryConjAction U Φ := by
  apply HCParams_eq_of_components
  · intro a
    show U * (Θ + Φ).A a * U.conjTranspose =
         U * Θ.A a * U.conjTranspose + U * Φ.A a * U.conjTranspose
    rw [HCParams_add_A, Matrix.mul_add, Matrix.add_mul]
  · intro b
    show U * (Θ + Φ).B b * U.conjTranspose =
         U * Θ.B b * U.conjTranspose + U * Φ.B b * U.conjTranspose
    rw [HCParams_add_B, Matrix.mul_add, Matrix.add_mul]
  · intro c
    show U * (Θ + Φ).C c * U.conjTranspose =
         U * Θ.C c * U.conjTranspose + U * Φ.C c * U.conjTranspose
    rw [HCParams_add_C, Matrix.mul_add, Matrix.add_mul]

/-- Unitary conjugation is `ℂ`-linear in `Θ`. -/
theorem unitaryConjAction_smul (U : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (Θ : HCParams n) :
    unitaryConjAction U (c • Θ) = c • unitaryConjAction U Θ := by
  apply HCParams_eq_of_components
  · intro a
    show U * (c • Θ).A a * U.conjTranspose = c • (U * Θ.A a * U.conjTranspose)
    rw [HCParams_smul_A, Matrix.mul_smul, Matrix.smul_mul]
  · intro b
    show U * (c • Θ).B b * U.conjTranspose = c • (U * Θ.B b * U.conjTranspose)
    rw [HCParams_smul_B, Matrix.mul_smul, Matrix.smul_mul]
  · intro c'
    show U * (c • Θ).C c' * U.conjTranspose = c • (U * Θ.C c' * U.conjTranspose)
    rw [HCParams_smul_C, Matrix.mul_smul, Matrix.smul_mul]

/-- Combined gauge action is additive in `Θ`. -/
theorem combinedGauge_add (U : Matrix (Fin n) (Fin n) ℂ) (sA sB sC : Fin n → ℂ)
    (Θ Φ : HCParams n) :
    combinedGauge U sA sB sC (Θ + Φ) =
    combinedGauge U sA sB sC Θ + combinedGauge U sA sB sC Φ := by
  unfold combinedGauge
  rw [gaugeAction_add, unitaryConjAction_add]

/-- Combined gauge action is `ℂ`-linear in `Θ`. -/
theorem combinedGauge_smul (U : Matrix (Fin n) (Fin n) ℂ) (sA sB sC : Fin n → ℂ)
    (c : ℂ) (Θ : HCParams n) :
    combinedGauge U sA sB sC (c • Θ) = c • combinedGauge U sA sB sC Θ := by
  unfold combinedGauge
  rw [gaugeAction_smul, unitaryConjAction_smul]

/-! ## Gauge actions as LinearMaps -/

/-- The per-slot gauge action packaged as a `ℂ`-linear endomorphism of `HCParams n`. -/
noncomputable def gaugeActionLinear (sA sB sC : Fin n → ℂ) :
    HCParams n →ₗ[ℂ] HCParams n where
  toFun := gaugeAction sA sB sC
  map_add' := gaugeAction_add sA sB sC
  map_smul' := gaugeAction_smul sA sB sC

@[simp] theorem gaugeActionLinear_apply (sA sB sC : Fin n → ℂ) (Θ : HCParams n) :
    gaugeActionLinear sA sB sC Θ = gaugeAction sA sB sC Θ := rfl

/-- The unitary-conjugation gauge action packaged as a `ℂ`-linear endomorphism. -/
noncomputable def unitaryConjActionLinear (U : Matrix (Fin n) (Fin n) ℂ) :
    HCParams n →ₗ[ℂ] HCParams n where
  toFun := unitaryConjAction U
  map_add' := unitaryConjAction_add U
  map_smul' := unitaryConjAction_smul U

@[simp] theorem unitaryConjActionLinear_apply (U : Matrix (Fin n) (Fin n) ℂ)
    (Θ : HCParams n) :
    unitaryConjActionLinear U Θ = unitaryConjAction U Θ := rfl

/-- The combined gauge action packaged as a `ℂ`-linear endomorphism. -/
noncomputable def combinedGaugeLinear (U : Matrix (Fin n) (Fin n) ℂ)
    (sA sB sC : Fin n → ℂ) : HCParams n →ₗ[ℂ] HCParams n where
  toFun := combinedGauge U sA sB sC
  map_add' := combinedGauge_add U sA sB sC
  map_smul' := combinedGauge_smul U sA sB sC

@[simp] theorem combinedGaugeLinear_apply (U : Matrix (Fin n) (Fin n) ℂ)
    (sA sB sC : Fin n → ℂ) (Θ : HCParams n) :
    combinedGaugeLinear U sA sB sC Θ = combinedGauge U sA sB sC Θ := rfl

/-- The uniform-scaling gauge action packaged as a `ℂ`-linear endomorphism. -/
noncomputable def uniformScaleLinear (t : ℂ) : HCParams n →ₗ[ℂ] HCParams n :=
  gaugeActionLinear (fun _ => t) (fun _ => t) (fun _ => t)

@[simp] theorem uniformScaleLinear_apply (t : ℂ) (Θ : HCParams n) :
    uniformScaleLinear t Θ = uniformScale t Θ := rfl

/-- LinearMap composition matches combinedGauge composition. -/
theorem combinedGaugeLinear_eq_comp (U : Matrix (Fin n) (Fin n) ℂ)
    (sA sB sC : Fin n → ℂ) :
    combinedGaugeLinear U sA sB sC =
    (unitaryConjActionLinear U).comp (gaugeActionLinear sA sB sC) := by
  ext Θ
  rfl

/-- The composition law `gaugeActionLinear ∘ gaugeActionLinear` corresponds to
    multiplicative factor combination. -/
theorem gaugeActionLinear_comp (sA₁ sB₁ sC₁ sA₂ sB₂ sC₂ : Fin n → ℂ) :
    (gaugeActionLinear sA₂ sB₂ sC₂).comp (gaugeActionLinear sA₁ sB₁ sC₁) =
    gaugeActionLinear (fun a => sA₂ a * sA₁ a) (fun b => sB₂ b * sB₁ b)
      (fun c => sC₂ c * sC₁ c) := by
  ext Θ
  exact gaugeAction_mul sA₁ sB₁ sC₁ sA₂ sB₂ sC₂ Θ

/-- The composition law `unitaryConjActionLinear` of two unitaries. -/
theorem unitaryConjActionLinear_comp (U₁ U₂ : Matrix (Fin n) (Fin n) ℂ) :
    (unitaryConjActionLinear U₂).comp (unitaryConjActionLinear U₁) =
    unitaryConjActionLinear (U₂ * U₁) := by
  ext Θ
  exact unitaryConjAction_mul U₁ U₂ Θ

/-- Trivial gauge as `LinearMap.id`. -/
@[simp] theorem gaugeActionLinear_one_eq_id :
    gaugeActionLinear (fun _ => (1 : ℂ)) (fun _ => 1) (fun _ => 1) =
    LinearMap.id (R := ℂ) (M := HCParams n) := by
  ext Θ
  exact gaugeAction_one Θ

@[simp] theorem unitaryConjActionLinear_one_eq_id :
    unitaryConjActionLinear (1 : Matrix (Fin n) (Fin n) ℂ) =
    LinearMap.id (R := ℂ) (M := HCParams n) := by
  ext Θ
  exact unitaryConjAction_one Θ

/-! ## Gauge actions as LinearEquivs (when invertible) -/

/-- The per-slot gauge action packaged as a `ℂ`-linear equivalence of `HCParams n`,
    when all per-slot factors are nonzero. -/
noncomputable def gaugeActionLinearEquiv (sA sB sC : Fin n → ℂ)
    (hA : ∀ a, sA a ≠ 0) (hB : ∀ b, sB b ≠ 0) (hC : ∀ c, sC c ≠ 0) :
    HCParams n ≃ₗ[ℂ] HCParams n where
  toFun := gaugeAction sA sB sC
  invFun := gaugeAction (fun a => (sA a)⁻¹) (fun b => (sB b)⁻¹) (fun c => (sC c)⁻¹)
  left_inv Θ := gaugeAction_inv sA sB sC hA hB hC Θ
  right_inv Ψ := by
    -- gaugeAction sA sB sC (gaugeAction (s⁻¹) Ψ) = Ψ
    have h_invA : ∀ a, (sA a)⁻¹ ≠ 0 := fun a => inv_ne_zero (hA a)
    have h_invB : ∀ b, (sB b)⁻¹ ≠ 0 := fun b => inv_ne_zero (hB b)
    have h_invC : ∀ c, (sC c)⁻¹ ≠ 0 := fun c => inv_ne_zero (hC c)
    -- Use gaugeAction_inv with the inverses
    have key := gaugeAction_inv (fun a => (sA a)⁻¹) (fun b => (sB b)⁻¹)
                  (fun c => (sC c)⁻¹) h_invA h_invB h_invC Ψ
    -- key: gaugeAction (s) (gaugeAction (s⁻¹) Ψ) = Ψ (after inv_inv)
    -- Need: gaugeAction sA sB sC (gaugeAction (sA⁻¹) (sB⁻¹) (sC⁻¹) Ψ) = Ψ
    convert key using 2 <;> funext _ <;> rw [inv_inv]
  map_add' := gaugeAction_add sA sB sC
  map_smul' := gaugeAction_smul sA sB sC

@[simp] theorem gaugeActionLinearEquiv_apply (sA sB sC : Fin n → ℂ)
    (hA : ∀ a, sA a ≠ 0) (hB : ∀ b, sB b ≠ 0) (hC : ∀ c, sC c ≠ 0) (Θ : HCParams n) :
    gaugeActionLinearEquiv sA sB sC hA hB hC Θ = gaugeAction sA sB sC Θ := rfl

@[simp] theorem gaugeActionLinearEquiv_symm_apply (sA sB sC : Fin n → ℂ)
    (hA : ∀ a, sA a ≠ 0) (hB : ∀ b, sB b ≠ 0) (hC : ∀ c, sC c ≠ 0) (Ψ : HCParams n) :
    (gaugeActionLinearEquiv sA sB sC hA hB hC).symm Ψ =
    gaugeAction (fun a => (sA a)⁻¹) (fun b => (sB b)⁻¹) (fun c => (sC c)⁻¹) Ψ := rfl

/-- The unitary-conjugation gauge action packaged as a `ℂ`-linear equivalence
    when `U` is unitary. -/
noncomputable def unitaryConjActionLinearEquiv (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1) :
    HCParams n ≃ₗ[ℂ] HCParams n where
  toFun := unitaryConjAction U
  invFun := unitaryConjAction U.conjTranspose
  left_inv Θ := unitaryConjAction_inv U hU Θ
  right_inv Ψ := unitaryConjAction_inv' U hU Ψ
  map_add' := unitaryConjAction_add U
  map_smul' := unitaryConjAction_smul U

@[simp] theorem unitaryConjActionLinearEquiv_apply (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1) (Θ : HCParams n) :
    unitaryConjActionLinearEquiv U hU Θ = unitaryConjAction U Θ := rfl

@[simp] theorem unitaryConjActionLinearEquiv_symm_apply (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1) (Ψ : HCParams n) :
    (unitaryConjActionLinearEquiv U hU).symm Ψ = unitaryConjAction U.conjTranspose Ψ := rfl

/-- The combined gauge action as a `ℂ`-linear equivalence when invertible
    (unitary `U` and nonzero per-slot factors). -/
noncomputable def combinedGaugeLinearEquiv (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1)
    (sA sB sC : Fin n → ℂ)
    (hA : ∀ a, sA a ≠ 0) (hB : ∀ b, sB b ≠ 0) (hC : ∀ c, sC c ≠ 0) :
    HCParams n ≃ₗ[ℂ] HCParams n :=
  (gaugeActionLinearEquiv sA sB sC hA hB hC).trans (unitaryConjActionLinearEquiv U hU)

@[simp] theorem combinedGaugeLinearEquiv_apply (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1)
    (sA sB sC : Fin n → ℂ)
    (hA : ∀ a, sA a ≠ 0) (hB : ∀ b, sB b ≠ 0) (hC : ∀ c, sC c ≠ 0) (Θ : HCParams n) :
    combinedGaugeLinearEquiv U hU sA sB sC hA hB hC Θ = combinedGauge U sA sB sC Θ := rfl

/-! ## Gauge actions as ContinuousLinearMaps -/

/-- The per-slot gauge action packaged as a continuous `ℂ`-linear map. -/
noncomputable def gaugeActionCLM (sA sB sC : Fin n → ℂ) :
    HCParams n →L[ℂ] HCParams n :=
  { gaugeActionLinear sA sB sC with
    cont := continuous_gaugeAction sA sB sC }

@[simp] theorem gaugeActionCLM_apply (sA sB sC : Fin n → ℂ) (Θ : HCParams n) :
    gaugeActionCLM sA sB sC Θ = gaugeAction sA sB sC Θ := rfl

@[simp] theorem gaugeActionCLM_toLinearMap (sA sB sC : Fin n → ℂ) :
    (gaugeActionCLM sA sB sC).toLinearMap = gaugeActionLinear sA sB sC := rfl

/-- Unitary conjugation as a continuous `ℂ`-linear map. -/
noncomputable def unitaryConjActionCLM (U : Matrix (Fin n) (Fin n) ℂ) :
    HCParams n →L[ℂ] HCParams n :=
  { unitaryConjActionLinear U with
    cont := continuous_unitaryConjAction U }

@[simp] theorem unitaryConjActionCLM_apply (U : Matrix (Fin n) (Fin n) ℂ)
    (Θ : HCParams n) :
    unitaryConjActionCLM U Θ = unitaryConjAction U Θ := rfl

@[simp] theorem unitaryConjActionCLM_toLinearMap (U : Matrix (Fin n) (Fin n) ℂ) :
    (unitaryConjActionCLM U).toLinearMap = unitaryConjActionLinear U := rfl

/-- Combined gauge action as a continuous `ℂ`-linear map. -/
noncomputable def combinedGaugeCLM (U : Matrix (Fin n) (Fin n) ℂ) (sA sB sC : Fin n → ℂ) :
    HCParams n →L[ℂ] HCParams n :=
  { combinedGaugeLinear U sA sB sC with
    cont := continuous_combinedGauge U sA sB sC }

@[simp] theorem combinedGaugeCLM_apply (U : Matrix (Fin n) (Fin n) ℂ)
    (sA sB sC : Fin n → ℂ) (Θ : HCParams n) :
    combinedGaugeCLM U sA sB sC Θ = combinedGauge U sA sB sC Θ := rfl

/-- Uniform scaling as a continuous `ℂ`-linear map. -/
noncomputable def uniformScaleCLM (t : ℂ) : HCParams n →L[ℂ] HCParams n :=
  gaugeActionCLM (fun _ => t) (fun _ => t) (fun _ => t)

@[simp] theorem uniformScaleCLM_apply (t : ℂ) (Θ : HCParams n) :
    uniformScaleCLM t Θ = uniformScale t Θ := rfl

/-- Composition formula for `gaugeActionCLM` matches multiplicative factor combination. -/
theorem gaugeActionCLM_comp (sA₁ sB₁ sC₁ sA₂ sB₂ sC₂ : Fin n → ℂ) :
    (gaugeActionCLM sA₂ sB₂ sC₂).comp (gaugeActionCLM sA₁ sB₁ sC₁) =
    gaugeActionCLM (fun a => sA₂ a * sA₁ a) (fun b => sB₂ b * sB₁ b)
      (fun c => sC₂ c * sC₁ c) := by
  ext Θ
  exact gaugeAction_mul sA₁ sB₁ sC₁ sA₂ sB₂ sC₂ Θ

/-- Composition formula for `unitaryConjActionCLM`. -/
theorem unitaryConjActionCLM_comp (U₁ U₂ : Matrix (Fin n) (Fin n) ℂ) :
    (unitaryConjActionCLM U₂).comp (unitaryConjActionCLM U₁) =
    unitaryConjActionCLM (U₂ * U₁) := by
  ext Θ
  exact unitaryConjAction_mul U₁ U₂ Θ

/-- Combined gauge as composition of unitary CLM and per-slot CLM. -/
theorem combinedGaugeCLM_eq_comp (U : Matrix (Fin n) (Fin n) ℂ) (sA sB sC : Fin n → ℂ) :
    combinedGaugeCLM U sA sB sC =
    (unitaryConjActionCLM U).comp (gaugeActionCLM sA sB sC) := by
  ext Θ
  rfl

/-! ## Gauge actions as ContinuousLinearEquivs (when invertible) -/

/-- The per-slot gauge action packaged as a continuous `ℂ`-linear equivalence. -/
noncomputable def gaugeActionCLE (sA sB sC : Fin n → ℂ)
    (hA : ∀ a, sA a ≠ 0) (hB : ∀ b, sB b ≠ 0) (hC : ∀ c, sC c ≠ 0) :
    HCParams n ≃L[ℂ] HCParams n :=
  { gaugeActionLinearEquiv sA sB sC hA hB hC with
    continuous_toFun := continuous_gaugeAction sA sB sC
    continuous_invFun := continuous_gaugeAction _ _ _ }

@[simp] theorem gaugeActionCLE_apply (sA sB sC : Fin n → ℂ)
    (hA : ∀ a, sA a ≠ 0) (hB : ∀ b, sB b ≠ 0) (hC : ∀ c, sC c ≠ 0) (Θ : HCParams n) :
    gaugeActionCLE sA sB sC hA hB hC Θ = gaugeAction sA sB sC Θ := rfl

@[simp] theorem gaugeActionCLE_symm_apply (sA sB sC : Fin n → ℂ)
    (hA : ∀ a, sA a ≠ 0) (hB : ∀ b, sB b ≠ 0) (hC : ∀ c, sC c ≠ 0) (Ψ : HCParams n) :
    (gaugeActionCLE sA sB sC hA hB hC).symm Ψ =
    gaugeAction (fun a => (sA a)⁻¹) (fun b => (sB b)⁻¹) (fun c => (sC c)⁻¹) Ψ := rfl

/-- Unitary conjugation as a continuous `ℂ`-linear equivalence when `U` is unitary. -/
noncomputable def unitaryConjActionCLE (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1) :
    HCParams n ≃L[ℂ] HCParams n :=
  { unitaryConjActionLinearEquiv U hU with
    continuous_toFun := continuous_unitaryConjAction U
    continuous_invFun := continuous_unitaryConjAction U.conjTranspose }

@[simp] theorem unitaryConjActionCLE_apply (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1) (Θ : HCParams n) :
    unitaryConjActionCLE U hU Θ = unitaryConjAction U Θ := rfl

@[simp] theorem unitaryConjActionCLE_symm_apply (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1) (Ψ : HCParams n) :
    (unitaryConjActionCLE U hU).symm Ψ = unitaryConjAction U.conjTranspose Ψ := rfl

/-- Combined gauge action as a continuous `ℂ`-linear equivalence. -/
noncomputable def combinedGaugeCLE (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1)
    (sA sB sC : Fin n → ℂ)
    (hA : ∀ a, sA a ≠ 0) (hB : ∀ b, sB b ≠ 0) (hC : ∀ c, sC c ≠ 0) :
    HCParams n ≃L[ℂ] HCParams n :=
  (gaugeActionCLE sA sB sC hA hB hC).trans (unitaryConjActionCLE U hU)

@[simp] theorem combinedGaugeCLE_apply (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1)
    (sA sB sC : Fin n → ℂ)
    (hA : ∀ a, sA a ≠ 0) (hB : ∀ b, sB b ≠ 0) (hC : ∀ c, sC c ≠ 0) (Θ : HCParams n) :
    combinedGaugeCLE U hU sA sB sC hA hB hC Θ = combinedGauge U sA sB sC Θ := rfl

/-! ## Combined gauge orbit lies in an hcNormSq level set -/

/-- The combined gauge orbit of `Θ` is contained in the hcNormSq level set of `Θ`. -/
theorem combinedGaugeOrbit_subset_hcNormSq_levelSet (Θ : HCParams n) :
    combinedGaugeOrbit Θ ⊆ { Ψ | Tikhonov.hcNormSq Ψ = Tikhonov.hcNormSq Θ } := by
  intro Ψ h
  exact hcNormSq_constant_on_combinedGaugeOrbit Θ Ψ h

/-- Same for the feasibility-preserving orbit. -/
theorem feasibleCombinedGaugeOrbit_subset_hcNormSq_levelSet (Θ : HCParams n) (f : BinOp n) :
    feasibleCombinedGaugeOrbit Θ f ⊆
    { Ψ | Tikhonov.hcNormSq Ψ = Tikhonov.hcNormSq Θ } := by
  intro Ψ h
  exact combinedGaugeOrbit_subset_hcNormSq_levelSet Θ
    (feasibleCombinedGaugeOrbit_subset Θ f h)

/-- The combined gauge orbit is contained in the objective level set. -/
theorem combinedGaugeOrbit_subset_objective_levelSet (Θ : HCParams n) (f : BinOp n) :
    combinedGaugeOrbit Θ ⊆ { Ψ | objective Ψ f = objective Θ f } := by
  intro Ψ h
  exact objective_constant_on_combinedGaugeOrbit Θ Ψ f h

/-- The feasibility-preserving orbit is contained in the kappaTriple level set
    (at every (a, b, c)). -/
theorem feasibleCombinedGaugeOrbit_subset_kappaTriple_levelSet
    (Θ : HCParams n) (f : BinOp n) (a b c : Fin n) :
    feasibleCombinedGaugeOrbit Θ f ⊆
    { Ψ | kappaTriple Ψ a b c = kappaTriple Θ a b c } := by
  intro Ψ h
  exact kappaTriple_constant_on_combinedGaugeOrbit Θ Ψ
    (feasibleCombinedGaugeOrbit_subset Θ f h) a b c

/-- The feasibility-preserving gauge orbit is contained in the set of
    UnitaryCollinear factorisations, when `Θ` itself is UnitaryCollinear. -/
theorem feasibleCombinedGaugeOrbit_subset_unitaryCollinear (Θ : HCParams n) (f : BinOp n)
    (huc : UnitaryCollinear Θ f) :
    feasibleCombinedGaugeOrbit Θ f ⊆ { Ψ | UnitaryCollinear Ψ f } := by
  intro Ψ h
  exact unitaryCollinear_of_feasibleCombinedGaugeOrbit f h huc

/-- The feasibility-preserving gauge orbit is contained in the set of
    Nondegenerate parameters, when `Θ` is Nondegenerate. -/
theorem feasibleCombinedGaugeOrbit_subset_nondegenerate (Θ : HCParams n) (f : BinOp n)
    (hnd : Nondegenerate Θ) :
    feasibleCombinedGaugeOrbit Θ f ⊆ { Ψ | Nondegenerate Ψ } := by
  intro Ψ h
  exact nondegenerate_of_combinedGaugeOrbit Θ Ψ
    (feasibleCombinedGaugeOrbit_subset Θ f h) hnd

/-- The feasibility-preserving orbit is contained in the feasibility set. -/
theorem feasibleCombinedGaugeOrbit_subset_feasible (Θ : HCParams n) (f : BinOp n)
    (hfeas : Factorizes Θ f) :
    feasibleCombinedGaugeOrbit Θ f ⊆ { Ψ | Factorizes Ψ f } := by
  intro Ψ h
  exact factorizes_of_feasibleCombinedGaugeOrbit f h hfeas

/-! ## Non-emptiness of gauge orbit intersections -/

/-- The combined gauge orbit is always non-empty (contains `Θ` itself). -/
theorem combinedGaugeOrbit_nonempty (Θ : HCParams n) :
    (combinedGaugeOrbit Θ).Nonempty :=
  ⟨Θ, mem_combinedGaugeOrbit_self Θ⟩

/-- The feasibility-preserving combined gauge orbit is always non-empty. -/
theorem feasibleCombinedGaugeOrbit_nonempty (Θ : HCParams n) (f : BinOp n) :
    (feasibleCombinedGaugeOrbit Θ f).Nonempty :=
  ⟨Θ, mem_feasibleCombinedGaugeOrbit_self Θ f⟩

/-- When `Θ` is `UnitaryCollinear`, the intersection of its feasibility-preserving
    gauge orbit with the UnitaryCollinear set is non-empty (contains `Θ`). -/
theorem feasibleCombinedGaugeOrbit_inter_unitaryCollinear_nonempty
    (Θ : HCParams n) (f : BinOp n) (huc : UnitaryCollinear Θ f) :
    (feasibleCombinedGaugeOrbit Θ f ∩ { Ψ | UnitaryCollinear Ψ f }).Nonempty :=
  ⟨Θ, mem_feasibleCombinedGaugeOrbit_self Θ f, huc⟩

/-- The combined gauge orbit, intersected with the Nondegenerate set, is non-empty
    when `Θ` is Nondegenerate. -/
theorem combinedGaugeOrbit_inter_nondegenerate_nonempty
    (Θ : HCParams n) (hnd : Nondegenerate Θ) :
    (combinedGaugeOrbit Θ ∩ { Ψ | Nondegenerate Ψ }).Nonempty :=
  ⟨Θ, mem_combinedGaugeOrbit_self Θ, hnd⟩

/-! ## Gauge orbit equals predicate-restricted orbit (when Θ has the property) -/

/-- When `Θ` is UnitaryCollinear, the feasibility-preserving gauge orbit and the
    intersection with UC give the same set (both equal the orbit). -/
theorem feasibleCombinedGaugeOrbit_eq_inter_unitaryCollinear
    (Θ : HCParams n) (f : BinOp n) (huc : UnitaryCollinear Θ f) :
    feasibleCombinedGaugeOrbit Θ f = feasibleCombinedGaugeOrbit Θ f ∩
      { Ψ | UnitaryCollinear Ψ f } := by
  apply Set.Subset.antisymm
  · intro Ψ h
    exact ⟨h, unitaryCollinear_of_feasibleCombinedGaugeOrbit f h huc⟩
  · exact Set.inter_subset_left

/-- When `Θ` is Nondegenerate, the combined gauge orbit equals its intersection
    with the Nondegenerate set. -/
theorem combinedGaugeOrbit_eq_inter_nondegenerate
    (Θ : HCParams n) (hnd : Nondegenerate Θ) :
    combinedGaugeOrbit Θ = combinedGaugeOrbit Θ ∩ { Ψ | Nondegenerate Ψ } := by
  apply Set.Subset.antisymm
  · intro Ψ h
    exact ⟨h, nondegenerate_of_combinedGaugeOrbit Θ Ψ h hnd⟩
  · exact Set.inter_subset_left

/-! ## Combined gauge orbit of the zero element -/

/-- The combined gauge orbit of `0` is `{0}` — every gauge action fixes the zero
    element of `HCParams n`. -/
theorem combinedGaugeOrbit_zero : combinedGaugeOrbit (0 : HCParams n) = {0} := by
  apply Set.Subset.antisymm
  · intro Ψ ⟨U, sA, sB, sC, _, _, _, _, hΨ⟩
    rw [hΨ]
    show combinedGauge U sA sB sC (0 : HCParams n) ∈ ({0} : Set (HCParams n))
    rw [combinedGauge_zero]
    exact rfl
  · intro Ψ hΨ
    rw [Set.mem_singleton_iff] at hΨ
    rw [hΨ]
    exact mem_combinedGaugeOrbit_self _

/-- The feasibility-preserving gauge orbit of `0` is `{0}`. -/
theorem feasibleCombinedGaugeOrbit_zero (f : BinOp n) :
    feasibleCombinedGaugeOrbit (0 : HCParams n) f = {0} := by
  apply Set.Subset.antisymm
  · intro Ψ ⟨U, sA, sB, sC, _, _, _, _, _, hΨ⟩
    rw [hΨ]
    show combinedGauge U sA sB sC (0 : HCParams n) ∈ ({0} : Set (HCParams n))
    rw [combinedGauge_zero]
    exact rfl
  · intro Ψ hΨ
    rw [Set.mem_singleton_iff] at hΨ
    rw [hΨ]
    exact mem_feasibleCombinedGaugeOrbit_self _ f

/-- The unitary gauge orbit of `0` is `{0}`. -/
theorem unitaryGaugeOrbit_zero : unitaryGaugeOrbit (0 : HCParams n) = {0} := by
  apply Set.Subset.antisymm
  · intro Ψ ⟨U, _, hΨ⟩
    rw [hΨ]
    show unitaryConjAction U (0 : HCParams n) ∈ ({0} : Set (HCParams n))
    rw [unitaryConjAction_zero]
    exact rfl
  · intro Ψ hΨ
    rw [Set.mem_singleton_iff] at hΨ
    rw [hΨ]
    exact mem_unitaryGaugeOrbit_self _

/-! ## Identification of `Module.smul` with `uniformScale` -/

/-- The `Module ℂ` scalar action on `HCParams n` matches `uniformScale`: scaling
    every slot by the same `c` is exactly multiplying the parameter triple by `c`. -/
theorem smul_eq_uniformScale (c : ℂ) (Θ : HCParams n) :
    c • Θ = uniformScale c Θ := by
  apply HCParams_eq_of_components <;>
  · intro _
    rfl

/-- Scalar smul by a cube root of unity is a member of the feasibility-preserving
    combined gauge orbit. -/
theorem smul_cubeRoot_mem_feasibleCombinedGaugeOrbit
    (t : ℂ) (ht : t ^ 3 = 1) (Θ : HCParams n) (f : BinOp n) :
    t • Θ ∈ feasibleCombinedGaugeOrbit Θ f := by
  rw [smul_eq_uniformScale]
  exact uniformScale_cubeRoot_mem_feasibleCombinedGaugeOrbit t ht Θ f

/-- Scalar smul by a unit-modulus complex is in the combined gauge orbit. -/
theorem smul_unit_mod_mem_combinedGaugeOrbit
    (t : ℂ) (ht : t * starRingEnd ℂ t = 1) (Θ : HCParams n) :
    t • Θ ∈ combinedGaugeOrbit Θ := by
  rw [smul_eq_uniformScale]
  exact uniformScale_mem_combinedGaugeOrbit_of_unit_mod t ht Θ

/-! ## Equality of orbits for equivalent points -/

/-- Equivalent points have equal combined gauge orbits. -/
theorem combinedGaugeOrbit_eq {Θ Ψ : HCParams n} (h : Ψ ∈ combinedGaugeOrbit Θ) :
    combinedGaugeOrbit Θ = combinedGaugeOrbit Ψ := by
  apply Set.Subset.antisymm
  · intro Φ h'
    -- Θ ∈ orbit Ψ (by symmetry), so Φ ∈ orbit Θ ⊆ orbit Ψ via transitivity.
    exact combinedGaugeOrbit_trans (combinedGaugeOrbit_symm h) h'
  · intro Φ h'
    -- Φ ∈ orbit Ψ, Ψ ∈ orbit Θ, so Φ ∈ orbit Θ via transitivity.
    exact combinedGaugeOrbit_trans h h'

/-- Equivalent points have equal feasibility-preserving combined gauge orbits. -/
theorem feasibleCombinedGaugeOrbit_eq {Θ Ψ : HCParams n} {f : BinOp n}
    (h : Ψ ∈ feasibleCombinedGaugeOrbit Θ f) :
    feasibleCombinedGaugeOrbit Θ f = feasibleCombinedGaugeOrbit Ψ f := by
  apply Set.Subset.antisymm
  · intro Φ h'
    exact feasibleCombinedGaugeOrbit_trans (feasibleCombinedGaugeOrbit_symm h) h'
  · intro Φ h'
    exact feasibleCombinedGaugeOrbit_trans h h'

/-- Two points are gauge-equivalent iff their orbits coincide. -/
theorem mem_combinedGaugeOrbit_iff_eq {Θ Ψ : HCParams n} :
    Ψ ∈ combinedGaugeOrbit Θ ↔ combinedGaugeOrbit Θ = combinedGaugeOrbit Ψ := by
  refine ⟨combinedGaugeOrbit_eq, fun h => ?_⟩
  rw [h]
  exact mem_combinedGaugeOrbit_self Ψ

/-- Same iff for the feasibility-preserving orbit. -/
theorem mem_feasibleCombinedGaugeOrbit_iff_eq {Θ Ψ : HCParams n} {f : BinOp n} :
    Ψ ∈ feasibleCombinedGaugeOrbit Θ f ↔
    feasibleCombinedGaugeOrbit Θ f = feasibleCombinedGaugeOrbit Ψ f := by
  refine ⟨feasibleCombinedGaugeOrbit_eq, fun h => ?_⟩
  rw [h]
  exact mem_feasibleCombinedGaugeOrbit_self Ψ f

/-! ## Orbit closure under further gauge action -/

/-- The combined gauge orbit is closed under further combined-gauge action by
    unit-modulus + unitary parameters: applying any such gauge to a member of the
    orbit gives another member. -/
theorem combinedGauge_mem_combinedGaugeOrbit {Θ Ψ : HCParams n}
    (h : Ψ ∈ combinedGaugeOrbit Θ)
    (U : Matrix (Fin n) (Fin n) ℂ) (sA sB sC : Fin n → ℂ)
    (hA : ∀ a, sA a * starRingEnd ℂ (sA a) = 1)
    (hB : ∀ b, sB b * starRingEnd ℂ (sB b) = 1)
    (hC : ∀ c, sC c * starRingEnd ℂ (sC c) = 1)
    (hU : U * U.conjTranspose = 1) :
    combinedGauge U sA sB sC Ψ ∈ combinedGaugeOrbit Θ := by
  -- combinedGauge U s Ψ ∈ orbit Ψ, and orbit Ψ = orbit Θ (by combinedGaugeOrbit_eq).
  have h1 : combinedGauge U sA sB sC Ψ ∈ combinedGaugeOrbit Ψ :=
    ⟨U, sA, sB, sC, hA, hB, hC, hU, rfl⟩
  rw [combinedGaugeOrbit_eq h]
  exact h1

/-- Same closure for the feasibility-preserving orbit (additionally requires the
    cocycle condition). -/
theorem combinedGauge_mem_feasibleCombinedGaugeOrbit {Θ Ψ : HCParams n} {f : BinOp n}
    (h : Ψ ∈ feasibleCombinedGaugeOrbit Θ f)
    (U : Matrix (Fin n) (Fin n) ℂ) (sA sB sC : Fin n → ℂ)
    (hA : ∀ a, sA a * starRingEnd ℂ (sA a) = 1)
    (hB : ∀ b, sB b * starRingEnd ℂ (sB b) = 1)
    (hC : ∀ c, sC c * starRingEnd ℂ (sC c) = 1)
    (h_cocycle : ∀ a b, sA a * sB b * sC (f.op a b) = 1)
    (hU : U * U.conjTranspose = 1) :
    combinedGauge U sA sB sC Ψ ∈ feasibleCombinedGaugeOrbit Θ f := by
  have h1 : combinedGauge U sA sB sC Ψ ∈ feasibleCombinedGaugeOrbit Ψ f :=
    ⟨U, sA, sB, sC, hA, hB, hC, h_cocycle, hU, rfl⟩
  rw [feasibleCombinedGaugeOrbit_eq h]
  exact h1

/-- Orbit of gauge-image equals orbit of original. -/
theorem combinedGaugeOrbit_combinedGauge (Θ : HCParams n)
    (U : Matrix (Fin n) (Fin n) ℂ) (sA sB sC : Fin n → ℂ)
    (hA : ∀ a, sA a * starRingEnd ℂ (sA a) = 1)
    (hB : ∀ b, sB b * starRingEnd ℂ (sB b) = 1)
    (hC : ∀ c, sC c * starRingEnd ℂ (sC c) = 1)
    (hU : U * U.conjTranspose = 1) :
    combinedGaugeOrbit (combinedGauge U sA sB sC Θ) = combinedGaugeOrbit Θ :=
  (combinedGaugeOrbit_eq ⟨U, sA, sB, sC, hA, hB, hC, hU, rfl⟩).symm

/-- Orbit of unitary-conjugated point equals orbit of original. -/
theorem combinedGaugeOrbit_unitaryConjAction (Θ : HCParams n)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U * U.conjTranspose = 1) :
    combinedGaugeOrbit (unitaryConjAction U Θ) = combinedGaugeOrbit Θ :=
  (combinedGaugeOrbit_eq (unitaryConjAction_mem_combinedGaugeOrbit U hU Θ)).symm

/-- Orbit of cube-root scaled point equals orbit of original. -/
theorem combinedGaugeOrbit_uniformScale_cubeRoot (Θ : HCParams n)
    (t : ℂ) (ht : t ^ 3 = 1) :
    combinedGaugeOrbit (uniformScale t Θ) = combinedGaugeOrbit Θ :=
  (combinedGaugeOrbit_eq (uniformScale_cubeRoot_mem_combinedGaugeOrbit t ht Θ)).symm

/-! ## Equivalence-class dichotomy: orbits equal or disjoint -/

/-- Two combined gauge orbits are either equal or disjoint. -/
theorem combinedGaugeOrbit_eq_or_disjoint (Θ Ψ : HCParams n) :
    combinedGaugeOrbit Θ = combinedGaugeOrbit Ψ ∨
    Disjoint (combinedGaugeOrbit Θ) (combinedGaugeOrbit Ψ) := by
  by_cases h : ∃ Φ, Φ ∈ combinedGaugeOrbit Θ ∧ Φ ∈ combinedGaugeOrbit Ψ
  · obtain ⟨Φ, hΦΘ, hΦΨ⟩ := h
    left
    rw [combinedGaugeOrbit_eq hΦΘ, combinedGaugeOrbit_eq hΦΨ]
  · right
    rw [Set.disjoint_iff_inter_eq_empty]
    push_neg at h
    ext Φ
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hΦΘ
    exact h Φ hΦΘ

/-- Two feasibility-preserving combined gauge orbits are either equal or disjoint. -/
theorem feasibleCombinedGaugeOrbit_eq_or_disjoint (Θ Ψ : HCParams n) (f : BinOp n) :
    feasibleCombinedGaugeOrbit Θ f = feasibleCombinedGaugeOrbit Ψ f ∨
    Disjoint (feasibleCombinedGaugeOrbit Θ f) (feasibleCombinedGaugeOrbit Ψ f) := by
  by_cases h : ∃ Φ, Φ ∈ feasibleCombinedGaugeOrbit Θ f ∧
                    Φ ∈ feasibleCombinedGaugeOrbit Ψ f
  · obtain ⟨Φ, hΦΘ, hΦΨ⟩ := h
    left
    rw [feasibleCombinedGaugeOrbit_eq hΦΘ, feasibleCombinedGaugeOrbit_eq hΦΨ]
  · right
    rw [Set.disjoint_iff_inter_eq_empty]
    push_neg at h
    ext Φ
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hΦΘ
    exact h Φ hΦΘ

/-! ## Support preservation under nonzero gauge action -/

/-- For nonzero per-slot factors, `hcProduct` preserves the zero/non-zero pattern.
    This corresponds to "Support Preservation via Scalar Tracking" in Appendix E
    of the manuscript: the transformed trace tensor has the same support as the
    original. -/
theorem hcProduct_eq_zero_iff_gaugeAction (sA sB sC : Fin n → ℂ)
    (hA : ∀ a, sA a ≠ 0) (hB : ∀ b, sB b ≠ 0) (hC : ∀ c, sC c ≠ 0)
    (Θ : HCParams n) (a b c : Fin n) :
    hcProduct (gaugeAction sA sB sC Θ) a b c = 0 ↔ hcProduct Θ a b c = 0 := by
  rw [hcProduct_gaugeAction]
  rw [mul_eq_zero, or_iff_right]
  intro h_factor
  apply mul_ne_zero (mul_ne_zero (hA a) (hB b)) (hC c)
  exact h_factor

/-- Support preservation: the support of the transformed `hcProduct` matches
    the support of the original. -/
theorem hcProduct_ne_zero_iff_gaugeAction (sA sB sC : Fin n → ℂ)
    (hA : ∀ a, sA a ≠ 0) (hB : ∀ b, sB b ≠ 0) (hC : ∀ c, sC c ≠ 0)
    (Θ : HCParams n) (a b c : Fin n) :
    hcProduct (gaugeAction sA sB sC Θ) a b c ≠ 0 ↔ hcProduct Θ a b c ≠ 0 :=
  not_congr (hcProduct_eq_zero_iff_gaugeAction sA sB sC hA hB hC Θ a b c)

/-- Same support preservation for unitary conjugation. -/
theorem hcProduct_eq_zero_iff_unitaryConjAction (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1) (Θ : HCParams n) (a b c : Fin n) :
    hcProduct (unitaryConjAction U Θ) a b c = 0 ↔ hcProduct Θ a b c = 0 := by
  rw [hcProduct_unitaryConjAction U hU]

/-- Combined: support of `hcProduct` is preserved by combinedGauge with nonzero
    per-slot factors and unitary `U`. -/
theorem hcProduct_eq_zero_iff_combinedGauge (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1)
    (sA sB sC : Fin n → ℂ)
    (hA : ∀ a, sA a ≠ 0) (hB : ∀ b, sB b ≠ 0) (hC : ∀ c, sC c ≠ 0)
    (Θ : HCParams n) (a b c : Fin n) :
    hcProduct (combinedGauge U sA sB sC Θ) a b c = 0 ↔ hcProduct Θ a b c = 0 := by
  unfold combinedGauge
  rw [hcProduct_eq_zero_iff_unitaryConjAction U hU,
      hcProduct_eq_zero_iff_gaugeAction sA sB sC hA hB hC]

/-! ## Factorizes characterization under combined gauge -/

/-- Factorizes is preserved under combinedGauge by unitary `U` and per-slot
    factors satisfying the support cocycle. -/
theorem factorizes_combinedGauge_of_cocycle (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1)
    (sA sB sC : Fin n → ℂ) (Θ : HCParams n) (f : BinOp n) (hfeas : Factorizes Θ f)
    (h_cocycle : ∀ a b, sA a * sB b * sC (f.op a b) = 1) :
    Factorizes (combinedGauge U sA sB sC Θ) f := by
  unfold combinedGauge
  apply factorizes_unitaryConjAction _ _ _ U hU
  exact (factorizes_gaugeAction_iff sA sB sC Θ f hfeas).mpr h_cocycle

/-- Conversely: if the gauge image is feasible, then the cocycle holds (assuming
    `U` is unitary and `Θ` was feasible). The unitary part is "free" since it
    preserves Factorizes; only the per-slot factors face the cocycle constraint. -/
theorem cocycle_of_factorizes_combinedGauge (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1)
    (sA sB sC : Fin n → ℂ) (Θ : HCParams n) (f : BinOp n) (hfeas : Factorizes Θ f)
    (h_gauge_feas : Factorizes (combinedGauge U sA sB sC Θ) f) :
    ∀ a b, sA a * sB b * sC (f.op a b) = 1 := by
  -- Inverse: combinedGauge feasibility implies gaugeAction feasibility (unitary
  -- preserves Factorizes both ways).
  have hUH : U.conjTranspose * U = 1 := mul_eq_one_comm.mp hU
  -- Apply unitaryConjAction U† to combinedGauge U sA sB sC Θ.
  have h_inv : unitaryConjAction U.conjTranspose (combinedGauge U sA sB sC Θ) =
      gaugeAction sA sB sC Θ := by
    unfold combinedGauge
    rw [unitaryConjAction_inv U hU]
  have h_gauge : Factorizes (gaugeAction sA sB sC Θ) f := by
    rw [← h_inv]
    exact factorizes_unitaryConjAction _ _ h_gauge_feas U.conjTranspose
      (unitary_conjTranspose hU)
  exact (factorizes_gaugeAction_iff sA sB sC Θ f hfeas).mp h_gauge

/-- Two-sided characterization: the combined gauge image is feasible iff the
    per-slot factors satisfy the support cocycle. -/
theorem factorizes_combinedGauge_iff (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1)
    (sA sB sC : Fin n → ℂ) (Θ : HCParams n) (f : BinOp n) (hfeas : Factorizes Θ f) :
    Factorizes (combinedGauge U sA sB sC Θ) f ↔
    ∀ a b, sA a * sB b * sC (f.op a b) = 1 :=
  ⟨cocycle_of_factorizes_combinedGauge U hU sA sB sC Θ f hfeas,
   factorizes_combinedGauge_of_cocycle U hU sA sB sC Θ f hfeas⟩

/-! ## hcProduct pointwise invariance under cocycle gauge for feasible Θ -/

/-- For a feasible `Θ`, gauge action by per-slot factors satisfying the support
    cocycle leaves `hcProduct` pointwise invariant (not just on the support — the
    off-support entries are zero in both, so equality is universal). -/
theorem hcProduct_gaugeAction_of_feasible_cocycle
    (sA sB sC : Fin n → ℂ) (Θ : HCParams n) (f : BinOp n) (hfeas : Factorizes Θ f)
    (h_cocycle : ∀ a b, sA a * sB b * sC (f.op a b) = 1) (a b c : Fin n) :
    hcProduct (gaugeAction sA sB sC Θ) a b c = hcProduct Θ a b c := by
  rw [hcProduct_gaugeAction]
  by_cases h : c = f.op a b
  · subst h
    -- On support: sA·sB·sC = 1 by cocycle, so factor multiplies by 1.
    rw [h_cocycle a b, one_mul]
  · -- Off support: hcProduct Θ a b c = 0 (by Factorizes), and 0 multiplied
    -- by any scalar is 0.
    have hzero : hcProduct Θ a b c = 0 := by
      have := hfeas a b c
      rwa [structureTensor, if_neg (Ne.symm h)] at this
    rw [hzero, mul_zero]

/-- `hcProduct` is pointwise invariant under combinedGauge with unitary `U`,
    cocycle-satisfying factors, and feasible `Θ`. -/
theorem hcProduct_combinedGauge_of_feasible_cocycle (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1)
    (sA sB sC : Fin n → ℂ) (Θ : HCParams n) (f : BinOp n) (hfeas : Factorizes Θ f)
    (h_cocycle : ∀ a b, sA a * sB b * sC (f.op a b) = 1) (a b c : Fin n) :
    hcProduct (combinedGauge U sA sB sC Θ) a b c = hcProduct Θ a b c := by
  unfold combinedGauge
  rw [hcProduct_unitaryConjAction U hU,
      hcProduct_gaugeAction_of_feasible_cocycle sA sB sC Θ f hfeas h_cocycle]

/-! ## hcProduct under uniformScale by cube root of unity -/

/-- For a cube root of unity `t`, `hcProduct` is invariant under `uniformScale t`. -/
theorem hcProduct_uniformScale_cubeRoot (t : ℂ) (ht : t ^ 3 = 1)
    (Θ : HCParams n) (a b c : Fin n) :
    hcProduct (uniformScale t Θ) a b c = hcProduct Θ a b c := by
  rw [hcProduct_uniformScale, ht, one_mul]

/-! ## kappa_one as a predicate lifted to the gauge quotient -/

/-- `kappa_one` (the κ=1 condition on support) lifted to the combined gauge
    quotient as a `Prop` predicate, parameterised by the BinOp `f`. -/
def CombinedGaugeQuotient.kappaOne (f : BinOp n) (q : CombinedGaugeQuotient n) : Prop :=
  q.liftOn (fun Θ => ∀ a b : Fin n, _root_.kappaTriple Θ a b (f.op a b) = 1)
    (fun Θ Ψ h => propext (kappa_one_iff_combinedGaugeOrbit f h))

@[simp] theorem CombinedGaugeQuotient.kappaOne_mk (f : BinOp n) (Θ : HCParams n) :
    CombinedGaugeQuotient.kappaOne f
      (Quotient.mk (combinedGaugeSetoid n) Θ) =
    (∀ a b : Fin n, _root_.kappaTriple Θ a b (f.op a b) = 1) := rfl

/-- `kappa_one` lifted to the feasibility-preserving quotient. -/
def FeasibleCombinedGaugeQuotient.kappaOne {f : BinOp n}
    (q : FeasibleCombinedGaugeQuotient n f) : Prop :=
  q.liftOn (fun Θ => ∀ a b : Fin n, _root_.kappaTriple Θ a b (f.op a b) = 1)
    (fun Θ Ψ h => propext (kappa_one_iff_combinedGaugeOrbit f
      (feasibleCombinedGaugeOrbit_subset Θ f h)))

@[simp] theorem FeasibleCombinedGaugeQuotient.kappaOne_mk (f : BinOp n)
    (Θ : HCParams n) :
    FeasibleCombinedGaugeQuotient.kappaOne
      (Quotient.mk (feasibleCombinedGaugeSetoid n f) Θ
        : FeasibleCombinedGaugeQuotient n f) =
    (∀ a b : Fin n, _root_.kappaTriple Θ a b (f.op a b) = 1) := rfl

/-! ## Optimal value at UnitaryCollinear quotient classes -/

/-- The objective evaluates exactly to `3n²` at any UnitaryCollinear class
    on the feasibility-preserving gauge quotient. -/
theorem unitaryCollinear_objective_eq_three_n_sq_feasibleQuotient
    {f : BinOp n} (q : FeasibleCombinedGaugeQuotient n f)
    (huc : FeasibleCombinedGaugeQuotient.UnitaryCollinear q) :
    (FeasibleCombinedGaugeQuotient.objective q).re = 3 * (n : ℝ) ^ 2 := by
  induction q using Quotient.ind with
  | _ Θ =>
    show (_root_.objective Θ f).re = 3 * (n : ℝ) ^ 2
    exact uc_objective_value Θ f huc

/-- The AM-GM lower bound is attained as equality at UnitaryCollinear classes. -/
theorem unitaryCollinear_inverseScalePenalty_eq_three_n_sq_feasibleQuotient
    {f : BinOp n} (q : FeasibleCombinedGaugeQuotient n f)
    (huc : FeasibleCombinedGaugeQuotient.UnitaryCollinear q) :
    (FeasibleCombinedGaugeQuotient.objective q).re =
    (FeasibleCombinedGaugeQuotient.inverseScalePenalty q).re ∧
    (FeasibleCombinedGaugeQuotient.inverseScalePenalty q).re = 3 * (n : ℝ) ^ 2 := by
  induction q using Quotient.ind with
  | _ Θ =>
    show (_root_.objective Θ f).re = (_root_.inverseScalePenalty Θ f).re ∧
         (_root_.inverseScalePenalty Θ f).re = 3 * (n : ℝ) ^ 2
    have huc' : _root_.UnitaryCollinear Θ f := huc
    -- objective = 3n² by uc_objective_value
    have h_obj : (_root_.objective Θ f).re = 3 * (n : ℝ) ^ 2 := uc_objective_value Θ f huc'
    -- objective = inverseScalePenalty + misalignmentPenalty (decomposition); UC means
    -- misalignmentPenalty = 0 (= PerfectCollinearity), so objective = inverseScalePenalty.
    have hnd : Nondegenerate Θ := {
      A_pos := fun a => by rw [frobNormSq_unitary_eq_one _ (huc'.unitaryA a)]; exact one_ne_zero,
      B_pos := fun b => by rw [frobNormSq_unitary_eq_one _ (huc'.unitaryB b)]; exact one_ne_zero,
      C_pos := fun c => by rw [frobNormSq_unitary_eq_one _ (huc'.unitaryC c)]; exact one_ne_zero }
    have h_dec : _root_.objective Θ f =
        _root_.inverseScalePenalty Θ f + _root_.misalignmentPenalty Θ f :=
      decomposition Θ f hnd
    have h_misalign : _root_.misalignmentPenalty Θ f = 0 := huc'.collinear
    have h_obj_eq_ip : _root_.objective Θ f = _root_.inverseScalePenalty Θ f := by
      rw [h_dec, h_misalign, add_zero]
    refine ⟨?_, ?_⟩
    · rw [h_obj_eq_ip]
    · rw [← h_obj_eq_ip, h_obj]

/-! ## Optimal quotient classes: characterization -/

/-- A quotient class `q` is **optimal** if its objective achieves the lower bound `3n²`. -/
def FeasibleCombinedGaugeQuotient.IsOptimal {f : BinOp n}
    (q : FeasibleCombinedGaugeQuotient n f) : Prop :=
  (FeasibleCombinedGaugeQuotient.objective q).re = 3 * (n : ℝ) ^ 2

/-- UnitaryCollinear classes are optimal. -/
theorem unitaryCollinear_isOptimal_feasibleQuotient
    {f : BinOp n} (q : FeasibleCombinedGaugeQuotient n f)
    (huc : FeasibleCombinedGaugeQuotient.UnitaryCollinear q) :
    FeasibleCombinedGaugeQuotient.IsOptimal q :=
  unitaryCollinear_objective_eq_three_n_sq_feasibleQuotient q huc

@[simp] theorem FeasibleCombinedGaugeQuotient.IsOptimal_mk (f : BinOp n) (Θ : HCParams n) :
    FeasibleCombinedGaugeQuotient.IsOptimal
      (Quotient.mk (feasibleCombinedGaugeSetoid n f) Θ
        : FeasibleCombinedGaugeQuotient n f) =
    ((_root_.objective Θ f).re = 3 * (n : ℝ) ^ 2) := rfl

/-- The infimum of the objective on the feasibility-preserving quotient is at
    least 3n² (AM-GM bound, via the existence of any UC representative). -/
theorem inverseScalePenalty_re_ge_3nsq_feasibleQuotient
    {f : BinOp n} (hq : _root_.IsQuasigroup f)
    (q : FeasibleCombinedGaugeQuotient n f)
    (huc : FeasibleCombinedGaugeQuotient.UnitaryCollinear q) :
    3 * (n : ℝ) ^ 2 ≤ (FeasibleCombinedGaugeQuotient.inverseScalePenalty q).re :=
  amgm_lower_bound_feasibleQuotient hq q huc

/-- For UC quotient classes, both `objective.re` and `inverseScalePenalty.re` equal `3n²`. -/
theorem unitaryCollinear_objective_inverseScalePenalty_both_eq_3nsq_feasibleQuotient
    {f : BinOp n} (q : FeasibleCombinedGaugeQuotient n f)
    (huc : FeasibleCombinedGaugeQuotient.UnitaryCollinear q) :
    (FeasibleCombinedGaugeQuotient.objective q).re = 3 * (n : ℝ) ^ 2 ∧
    (FeasibleCombinedGaugeQuotient.inverseScalePenalty q).re = 3 * (n : ℝ) ^ 2 := by
  refine ⟨unitaryCollinear_objective_eq_three_n_sq_feasibleQuotient q huc, ?_⟩
  exact (unitaryCollinear_inverseScalePenalty_eq_three_n_sq_feasibleQuotient q huc).2

/-- An optimal feasibility-preserving quotient class with a feasibility witness
    is UnitaryCollinear. Direct consequence of `theorem9_absolute_feasible_bound_rigidity`
    (axiom-free). -/
theorem isOptimal_imp_unitaryCollinear_feasibleQuotient
    {f : BinOp n} (hq : _root_.IsQuasigroup f)
    (q : FeasibleCombinedGaugeQuotient n f)
    (hfeas_q : FeasibleCombinedGaugeQuotient.Factorizes q)
    (hopt : FeasibleCombinedGaugeQuotient.IsOptimal q) :
    FeasibleCombinedGaugeQuotient.UnitaryCollinear q := by
  induction q using Quotient.ind with
  | _ Θ =>
    show _root_.UnitaryCollinear Θ f
    have hfeas : Factorizes Θ f := hfeas_q
    exact (theorem9_absolute_feasible_bound_rigidity f hq Θ hfeas).mp hopt

/-- Iff form: a feasible quotient class is optimal iff it is UnitaryCollinear. -/
theorem isOptimal_iff_unitaryCollinear_feasibleQuotient
    {f : BinOp n} (hq : _root_.IsQuasigroup f)
    (q : FeasibleCombinedGaugeQuotient n f)
    (hfeas_q : FeasibleCombinedGaugeQuotient.Factorizes q) :
    FeasibleCombinedGaugeQuotient.IsOptimal q ↔
    FeasibleCombinedGaugeQuotient.UnitaryCollinear q :=
  ⟨isOptimal_imp_unitaryCollinear_feasibleQuotient hq q hfeas_q,
   unitaryCollinear_isOptimal_feasibleQuotient q⟩

/-- AM-GM lower bound at the feasibility-preserving gauge quotient (general
    case): for any feasible quotient class, the objective.re is at least 3n².
    Direct lift of `theorem9_absolute_feasible_bound_lower` to the quotient. -/
theorem theorem9_absolute_feasible_bound_lower_feasibleQuotient
    {f : BinOp n} (q : FeasibleCombinedGaugeQuotient n f)
    (hfeas_q : FeasibleCombinedGaugeQuotient.Factorizes q) :
    3 * (n : ℝ) ^ 2 ≤ (FeasibleCombinedGaugeQuotient.objective q).re := by
  induction q using Quotient.ind with
  | _ Θ =>
    show 3 * (n : ℝ) ^ 2 ≤ (_root_.objective Θ f).re
    exact theorem9_absolute_feasible_bound_lower f Θ hfeas_q

/-- Strict gap at the gauge-quotient level (Theorem 10 case 2): if `f` is not
    a group isotope, every feasible quotient class is strictly above 3n². -/
theorem theorem10_case2_strict_gap_non_group_feasibleQuotient
    {f : BinOp n} (hq : _root_.IsQuasigroup f) (hnotgi : ¬ _root_.IsGroupIsotope f)
    (q : FeasibleCombinedGaugeQuotient n f)
    (hfeas_q : FeasibleCombinedGaugeQuotient.Factorizes q) :
    (FeasibleCombinedGaugeQuotient.objective q).re > 3 * (n : ℝ) ^ 2 := by
  induction q using Quotient.ind with
  | _ Θ =>
    show (_root_.objective Θ f).re > 3 * (n : ℝ) ^ 2
    exact strict_gap_non_group_unconditional f hq hnotgi Θ hfeas_q

/-- No-optimal characterization at the gauge quotient: if `f` is not a group
    isotope, no feasible quotient class is optimal. -/
theorem not_isOptimal_of_non_group_feasibleQuotient
    {f : BinOp n} (hq : _root_.IsQuasigroup f) (hnotgi : ¬ _root_.IsGroupIsotope f)
    (q : FeasibleCombinedGaugeQuotient n f)
    (hfeas_q : FeasibleCombinedGaugeQuotient.Factorizes q) :
    ¬ FeasibleCombinedGaugeQuotient.IsOptimal q := by
  intro hopt
  -- IsOptimal says objective.re = 3n²; strict gap says objective.re > 3n².
  have h_strict := theorem10_case2_strict_gap_non_group_feasibleQuotient hq hnotgi q hfeas_q
  -- `hopt : (q.objective).re = 3 * n²` and `h_strict : (q.objective).re > 3 * n²`
  exact absurd hopt (ne_of_gt h_strict)

/-- Trichotomy at the gauge quotient: a feasible class is either optimal (and
    `f` is a group isotope) or strictly above the lower bound. -/
theorem feasibleQuotient_optimal_or_strict
    {f : BinOp n} (hq : _root_.IsQuasigroup f)
    (q : FeasibleCombinedGaugeQuotient n f)
    (hfeas_q : FeasibleCombinedGaugeQuotient.Factorizes q) :
    FeasibleCombinedGaugeQuotient.IsOptimal q ∨
    (FeasibleCombinedGaugeQuotient.objective q).re > 3 * (n : ℝ) ^ 2 := by
  by_cases hopt : FeasibleCombinedGaugeQuotient.IsOptimal q
  · exact Or.inl hopt
  · -- IsOptimal is `objective.re = 3n²`. Negation + lower bound gives strict.
    refine Or.inr ?_
    have h_le : 3 * (n : ℝ) ^ 2 ≤ (FeasibleCombinedGaugeQuotient.objective q).re :=
      theorem9_absolute_feasible_bound_lower_feasibleQuotient q hfeas_q
    have h_ne : (FeasibleCombinedGaugeQuotient.objective q).re ≠ 3 * (n : ℝ) ^ 2 := by
      intro heq
      exact hopt heq
    exact lt_of_le_of_ne h_le (Ne.symm h_ne)

/-- The real part of `objective` is constant on the combined gauge orbit. -/
theorem objective_re_constant_on_combinedGaugeOrbit
    (Θ Ψ : HCParams n) (f : BinOp n) (h : Ψ ∈ combinedGaugeOrbit Θ) :
    (objective Ψ f).re = (objective Θ f).re := by
  rw [objective_constant_on_combinedGaugeOrbit Θ Ψ f h]

/-- The real part of `inverseScalePenalty` is constant on the combined gauge orbit. -/
theorem inverseScalePenalty_re_constant_on_combinedGaugeOrbit
    (Θ Ψ : HCParams n) (f : BinOp n) (h : Ψ ∈ combinedGaugeOrbit Θ) :
    (inverseScalePenalty Ψ f).re = (inverseScalePenalty Θ f).re := by
  rw [inverseScalePenalty_constant_on_combinedGaugeOrbit Θ Ψ f h]

/-- The real part of `hcNormSq` is constant on the combined gauge orbit. -/
theorem hcNormSq_re_constant_on_combinedGaugeOrbit
    (Θ Ψ : HCParams n) (h : Ψ ∈ combinedGaugeOrbit Θ) :
    (Tikhonov.hcNormSq Ψ).re = (Tikhonov.hcNormSq Θ).re := by
  rw [hcNormSq_constant_on_combinedGaugeOrbit Θ Ψ h]

/-- The real part of `misalignmentPenalty` is constant on the combined gauge orbit
    (requires Nondegenerate at the source point). -/
theorem misalignmentPenalty_re_constant_on_combinedGaugeOrbit
    (Θ Ψ : HCParams n) (f : BinOp n)
    (h : Ψ ∈ combinedGaugeOrbit Θ) (hnd : Nondegenerate Θ) :
    (misalignmentPenalty Ψ f).re = (misalignmentPenalty Θ f).re := by
  rw [misalignmentPenalty_constant_on_combinedGaugeOrbit Θ Ψ f h hnd]

/-- For any group isotope `f`, an `IsOptimal` quotient class exists on the
    feasibility-preserving combined gauge quotient. Specialisation of
    `exists_isOptimal_iff_group_isotope_feasibleQuotient` (forward direction). -/
theorem isGroupIsotope_imp_exists_isOptimal_feasibleQuotient
    {f : BinOp n} (hq : _root_.IsQuasigroup f) (hgi : _root_.IsGroupIsotope f) :
    ∃ q : FeasibleCombinedGaugeQuotient n f,
      FeasibleCombinedGaugeQuotient.Factorizes q ∧
      FeasibleCombinedGaugeQuotient.IsOptimal q := by
  obtain ⟨Θ_opt, huc⟩ := lemma14_group_isotope_admits_unitary_collinear f hq hgi
  refine ⟨Quotient.mk (feasibleCombinedGaugeSetoid n f) Θ_opt, ?_, ?_⟩
  · -- Factorizes_mk simp lemma
    show _root_.Factorizes Θ_opt f
    exact huc.feasible
  · -- IsOptimal_mk simp lemma: objective.re = 3n²
    show (_root_.objective Θ_opt f).re = 3 * (n : ℝ) ^ 2
    exact uc_objective_value Θ_opt f huc

/-- Conversely, existence of an IsOptimal feasible quotient class implies `f` is
    a group isotope. -/
theorem exists_isOptimal_feasibleQuotient_imp_isGroupIsotope
    {f : BinOp n} (hq : _root_.IsQuasigroup f)
    (hex : ∃ q : FeasibleCombinedGaugeQuotient n f,
      FeasibleCombinedGaugeQuotient.Factorizes q ∧
      FeasibleCombinedGaugeQuotient.IsOptimal q) :
    _root_.IsGroupIsotope f := by
  obtain ⟨q, hfeas_q, hopt_q⟩ := hex
  induction q using Quotient.ind with
  | _ Θ =>
    have hfeas : _root_.Factorizes Θ f := hfeas_q
    have hH : (_root_.objective Θ f).re = 3 * (n : ℝ) ^ 2 := hopt_q
    have huc : _root_.UnitaryCollinear Θ f :=
      (theorem9_absolute_feasible_bound_rigidity f hq Θ hfeas).mp hH
    exact unitary_collinear_implies_group_isotope f hq ⟨Θ, huc⟩

/-- **Theorem 10 at the gauge-quotient level.** Both cases of the manuscript's
    Associativity Gap dichotomy, stated entirely on the gauge quotient. -/
theorem theorem10_global_optimality_dichotomy_feasibleQuotient {f : BinOp n}
    (hq : _root_.IsQuasigroup f) :
    (_root_.IsGroupIsotope f →
      ∃ q : FeasibleCombinedGaugeQuotient n f,
        FeasibleCombinedGaugeQuotient.Factorizes q ∧
        FeasibleCombinedGaugeQuotient.IsOptimal q) ∧
    (¬ _root_.IsGroupIsotope f →
      ∀ q : FeasibleCombinedGaugeQuotient n f,
        FeasibleCombinedGaugeQuotient.Factorizes q →
        (FeasibleCombinedGaugeQuotient.objective q).re > 3 * (n : ℝ) ^ 2) := by
  refine ⟨?_, ?_⟩
  · exact isGroupIsotope_imp_exists_isOptimal_feasibleQuotient hq
  · intro hnotgi q hfeas_q
    exact theorem10_case2_strict_gap_non_group_feasibleQuotient hq hnotgi q hfeas_q

/-- The optimal class is unique up to gauge equivalence: any two UnitaryCollinear
    feasible quotient classes coincide as quotient elements. (Manuscript Lemma
    13 in the new numbering, `lem:app_representation_uniqueness`: representation
    uniqueness via character theory — but here we use the weaker gauge-orbit
    characterization rather than invoking Lemma 13 directly.) -/
theorem unitaryCollinear_classes_share_objective_feasibleQuotient
    {f : BinOp n} (q₁ q₂ : FeasibleCombinedGaugeQuotient n f)
    (huc₁ : FeasibleCombinedGaugeQuotient.UnitaryCollinear q₁)
    (huc₂ : FeasibleCombinedGaugeQuotient.UnitaryCollinear q₂) :
    (FeasibleCombinedGaugeQuotient.objective q₁).re =
    (FeasibleCombinedGaugeQuotient.objective q₂).re := by
  rw [unitaryCollinear_objective_eq_three_n_sq_feasibleQuotient q₁ huc₁,
      unitaryCollinear_objective_eq_three_n_sq_feasibleQuotient q₂ huc₂]

/-- For a UnitaryCollinear factorisation Θ, `hcNormSq Θ = 3n` (each of the
    `3n` slots has Frobenius norm-squared 1). -/
theorem hcNormSq_unitaryCollinear (Θ : HCParams n) (f : BinOp n)
    (huc : _root_.UnitaryCollinear Θ f) :
    Tikhonov.hcNormSq Θ = 3 * (n : ℂ) := by
  unfold Tikhonov.hcNormSq
  have hA : ∀ a, frobNormSq (Θ.A a) = 1 :=
    fun a => frobNormSq_unitary_eq_one (Θ.A a) (huc.unitaryA a)
  have hB : ∀ b, frobNormSq (Θ.B b) = 1 :=
    fun b => frobNormSq_unitary_eq_one (Θ.B b) (huc.unitaryB b)
  have hC : ∀ c, frobNormSq (Θ.C c) = 1 :=
    fun c => frobNormSq_unitary_eq_one (Θ.C c) (huc.unitaryC c)
  rw [show (∑ a : Fin n, frobNormSq (Θ.A a)) = ∑ _ : Fin n, (1 : ℂ) from
        Finset.sum_congr rfl (fun a _ => hA a),
      show (∑ b : Fin n, frobNormSq (Θ.B b)) = ∑ _ : Fin n, (1 : ℂ) from
        Finset.sum_congr rfl (fun b _ => hB b),
      show (∑ c : Fin n, frobNormSq (Θ.C c)) = ∑ _ : Fin n, (1 : ℂ) from
        Finset.sum_congr rfl (fun c _ => hC c)]
  simp [Finset.card_univ, Fintype.card_fin]
  ring

/-- For a UnitaryCollinear feasible quotient class, the lifted hcNormSq equals
    `3n`. -/
theorem hcNormSq_unitaryCollinear_feasibleQuotient
    {f : BinOp n} (q : FeasibleCombinedGaugeQuotient n f)
    (huc : FeasibleCombinedGaugeQuotient.UnitaryCollinear q) :
    FeasibleCombinedGaugeQuotient.hcNormSq q = 3 * (n : ℂ) := by
  induction q using Quotient.ind with
  | _ Θ =>
    show Tikhonov.hcNormSq Θ = 3 * (n : ℂ)
    exact hcNormSq_unitaryCollinear Θ f huc

/-- Real-part version: for a UnitaryCollinear factorisation, `hcNormSq.re = 3n`. -/
theorem hcNormSq_re_unitaryCollinear (Θ : HCParams n) (f : BinOp n)
    (huc : _root_.UnitaryCollinear Θ f) :
    (Tikhonov.hcNormSq Θ).re = 3 * (n : ℝ) := by
  rw [hcNormSq_unitaryCollinear Θ f huc]
  simp [Complex.mul_re, Complex.natCast_re, Complex.natCast_im]

/-- Real-part version at the gauge quotient: `hcNormSq.re = 3n` for UC classes. -/
theorem hcNormSq_re_unitaryCollinear_feasibleQuotient
    {f : BinOp n} (q : FeasibleCombinedGaugeQuotient n f)
    (huc : FeasibleCombinedGaugeQuotient.UnitaryCollinear q) :
    (FeasibleCombinedGaugeQuotient.hcNormSq q).re = 3 * (n : ℝ) := by
  induction q using Quotient.ind with
  | _ Θ =>
    show (Tikhonov.hcNormSq Θ).re = 3 * (n : ℝ)
    exact hcNormSq_re_unitaryCollinear Θ f huc

/-- Two UC feasible quotient classes share the same hcNormSq value (`3n`). -/
theorem unitaryCollinear_classes_share_hcNormSq_feasibleQuotient
    {f : BinOp n} (q₁ q₂ : FeasibleCombinedGaugeQuotient n f)
    (huc₁ : FeasibleCombinedGaugeQuotient.UnitaryCollinear q₁)
    (huc₂ : FeasibleCombinedGaugeQuotient.UnitaryCollinear q₂) :
    FeasibleCombinedGaugeQuotient.hcNormSq q₁ =
    FeasibleCombinedGaugeQuotient.hcNormSq q₂ := by
  rw [hcNormSq_unitaryCollinear_feasibleQuotient q₁ huc₁,
      hcNormSq_unitaryCollinear_feasibleQuotient q₂ huc₂]

/-- The real-part version: two UC classes share the same hcNormSq.re (`3n`). -/
theorem unitaryCollinear_classes_share_hcNormSq_re_feasibleQuotient
    {f : BinOp n} (q₁ q₂ : FeasibleCombinedGaugeQuotient n f)
    (huc₁ : FeasibleCombinedGaugeQuotient.UnitaryCollinear q₁)
    (huc₂ : FeasibleCombinedGaugeQuotient.UnitaryCollinear q₂) :
    (FeasibleCombinedGaugeQuotient.hcNormSq q₁).re =
    (FeasibleCombinedGaugeQuotient.hcNormSq q₂).re := by
  rw [hcNormSq_re_unitaryCollinear_feasibleQuotient q₁ huc₁,
      hcNormSq_re_unitaryCollinear_feasibleQuotient q₂ huc₂]

/-- Two-sided iff: under combinedGauge with cocycle, feasibility is invariant. -/
theorem factorizes_combinedGauge_of_cocycle_iff (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1)
    (sA sB sC : Fin n → ℂ) (Θ : HCParams n) (f : BinOp n)
    (hA : ∀ a, sA a ≠ 0) (hB : ∀ b, sB b ≠ 0) (hC : ∀ c, sC c ≠ 0)
    (h_cocycle : ∀ a b, sA a * sB b * sC (f.op a b) = 1) :
    Factorizes (combinedGauge U sA sB sC Θ) f ↔ Factorizes Θ f := by
  refine ⟨?_, ?_⟩
  · intro h_gauge
    -- Use the inverse gauge: combinedGauge U† s⁻¹ undoes the action.
    have h_inv : Θ = combinedGauge U.conjTranspose
        (fun a => (sA a)⁻¹) (fun b => (sB b)⁻¹) (fun c => (sC c)⁻¹)
        (combinedGauge U sA sB sC Θ) :=
      (combinedGauge_inv U hU sA sB sC hA hB hC Θ).symm
    rw [h_inv]
    -- Inverse gauge has inverse cocycle: (sA⁻¹)(a) · (sB⁻¹)(b) · (sC⁻¹)(c) =
    -- (sA(a) · sB(b) · sC(c))⁻¹ = 1⁻¹ = 1.
    have h_inv_cocycle : ∀ a b, (sA a)⁻¹ * (sB b)⁻¹ * (sC (f.op a b))⁻¹ = 1 := by
      intro a b
      rw [show (sA a)⁻¹ * (sB b)⁻¹ * (sC (f.op a b))⁻¹ =
            (sA a * sB b * sC (f.op a b))⁻¹ from by
        rw [mul_inv, mul_inv]]
      rw [h_cocycle a b, inv_one]
    apply factorizes_combinedGauge_of_cocycle U.conjTranspose
      (unitary_conjTranspose hU) _ _ _ _ f h_gauge h_inv_cocycle
  · intro h_orig
    exact factorizes_combinedGauge_of_cocycle U hU sA sB sC Θ f h_orig h_cocycle

/-- Two UnitaryCollinear feasible quotient classes share the same kappaTriple
    values on support (both equal 1). -/
theorem unitaryCollinear_classes_share_kappaTriple_feasibleQuotient
    {f : BinOp n} (hq : _root_.IsQuasigroup f)
    (q₁ q₂ : FeasibleCombinedGaugeQuotient n f)
    (huc₁ : FeasibleCombinedGaugeQuotient.UnitaryCollinear q₁)
    (huc₂ : FeasibleCombinedGaugeQuotient.UnitaryCollinear q₂)
    (hfeas₁ : FeasibleCombinedGaugeQuotient.Factorizes q₁)
    (hfeas₂ : FeasibleCombinedGaugeQuotient.Factorizes q₂)
    (a b : Fin n) :
    FeasibleCombinedGaugeQuotient.kappaTriple a b (f.op a b) q₁ =
    FeasibleCombinedGaugeQuotient.kappaTriple a b (f.op a b) q₂ := by
  -- For each UC class, kappaTriple a b (f.op a b) = 1.
  have h₁ : FeasibleCombinedGaugeQuotient.kappaTriple a b (f.op a b) q₁ = 1 := by
    induction q₁ using Quotient.ind with
    | _ Θ =>
      show _root_.kappaTriple Θ a b (f.op a b) = 1
      have huc' : _root_.UnitaryCollinear Θ f := huc₁
      have hfeas : Factorizes Θ f := hfeas₁
      have hT : hcProduct Θ a b (f.op a b) = 1 := by
        have := hfeas a b (f.op a b)
        rwa [structureTensor, if_pos rfl] at this
      have hnA : frobNormSq (Θ.A a) = 1 := frobNormSq_unitary_eq_one (Θ.A a) (huc'.unitaryA a)
      have hnB : frobNormSq (Θ.B b) = 1 := frobNormSq_unitary_eq_one (Θ.B b) (huc'.unitaryB b)
      have hnC : frobNormSq (Θ.C (f.op a b)) = 1 :=
        frobNormSq_unitary_eq_one (Θ.C (f.op a b)) (huc'.unitaryC (f.op a b))
      unfold kappaTriple
      rw [hnA, hnB, hnC, hT]
      simp
  have h₂ : FeasibleCombinedGaugeQuotient.kappaTriple a b (f.op a b) q₂ = 1 := by
    induction q₂ using Quotient.ind with
    | _ Θ =>
      show _root_.kappaTriple Θ a b (f.op a b) = 1
      have huc' : _root_.UnitaryCollinear Θ f := huc₂
      have hfeas : Factorizes Θ f := hfeas₂
      have hT : hcProduct Θ a b (f.op a b) = 1 := by
        have := hfeas a b (f.op a b)
        rwa [structureTensor, if_pos rfl] at this
      have hnA : frobNormSq (Θ.A a) = 1 := frobNormSq_unitary_eq_one (Θ.A a) (huc'.unitaryA a)
      have hnB : frobNormSq (Θ.B b) = 1 := frobNormSq_unitary_eq_one (Θ.B b) (huc'.unitaryB b)
      have hnC : frobNormSq (Θ.C (f.op a b)) = 1 :=
        frobNormSq_unitary_eq_one (Θ.C (f.op a b)) (huc'.unitaryC (f.op a b))
      unfold kappaTriple
      rw [hnA, hnB, hnC, hT]
      simp
  rw [h₁, h₂]

/-- Optimum value characterization: for a feasible group-isotope `f`, the
    minimum of `ℋ(Θ).re` over feasible Θ equals exactly `3n²`, attained by
    UnitaryCollinear factorisations. Combines Theorem 9 (Absolute Feasible
    Bound — both halves: lower bound and equality rigidity) with Theorem 4
    (UC ⟺ group isotope). -/
theorem optimum_value_eq_three_n_sq_iff_group_isotope
    (f : BinOp n) (hq : _root_.IsQuasigroup f) :
    (∃ Θ : HCParams n, Factorizes Θ f ∧
      (_root_.objective Θ f).re = 3 * (n : ℝ) ^ 2) ↔
    _root_.IsGroupIsotope f := by
  refine ⟨?_, ?_⟩
  · rintro ⟨Θ, hfeas, hH⟩
    have huc : _root_.UnitaryCollinear Θ f :=
      (theorem9_absolute_feasible_bound_rigidity f hq Θ hfeas).mp hH
    exact unitary_collinear_implies_group_isotope f hq ⟨Θ, huc⟩
  · intro hgi
    obtain ⟨Θ_opt, huc⟩ := lemma14_group_isotope_admits_unitary_collinear f hq hgi
    exact ⟨Θ_opt, huc.feasible, uc_objective_value Θ_opt f huc⟩


/-- Decomposition inequality at the quotient: inverseScalePenalty ≤ objective. -/
theorem inverseScalePenalty_le_objective_feasibleQuotient
    {f : BinOp n} (hq : _root_.IsQuasigroup f)
    (q : FeasibleCombinedGaugeQuotient n f)
    (hfeas_q : FeasibleCombinedGaugeQuotient.Factorizes q) :
    (FeasibleCombinedGaugeQuotient.inverseScalePenalty q).re ≤
    (FeasibleCombinedGaugeQuotient.objective q).re := by
  induction q using Quotient.ind with
  | _ Θ =>
    show (_root_.inverseScalePenalty Θ f).re ≤ (_root_.objective Θ f).re
    have hfeas : Factorizes Θ f := hfeas_q
    have hnd := factorizes_implies_nondegenerate Θ f hq hfeas
    have hdec : _root_.objective Θ f =
        _root_.inverseScalePenalty Θ f + _root_.misalignmentPenalty Θ f :=
      decomposition Θ f hnd
    have hR_re_nn : 0 ≤ (_root_.misalignmentPenalty Θ f).re := by
      have := misalignmentPenalty_nonneg Θ f
      exact this
    have hsum_re : (_root_.objective Θ f).re =
        (_root_.inverseScalePenalty Θ f).re + (_root_.misalignmentPenalty Θ f).re := by
      rw [hdec]; exact Complex.add_re _ _
    linarith

/-- An IsOptimal class exists on the feasibility-preserving gauge quotient if
    and only if `f` is a group isotope. Lifts Theorem 10 / 4 to the quotient
    level (axiom-free). -/
theorem exists_isOptimal_iff_group_isotope_feasibleQuotient
    {f : BinOp n} (hq : _root_.IsQuasigroup f) :
    (∃ Θ : HCParams n, Factorizes Θ f ∧
      FeasibleCombinedGaugeQuotient.IsOptimal
        (Quotient.mk (feasibleCombinedGaugeSetoid n f) Θ
          : FeasibleCombinedGaugeQuotient n f)) ↔
    _root_.IsGroupIsotope f := by
  refine ⟨?_, ?_⟩
  · rintro ⟨Θ, hfeas, hopt⟩
    -- IsOptimal_mk says (objective Θ f).re = 3 * n²
    have hH : (_root_.objective Θ f).re = 3 * (n : ℝ) ^ 2 := hopt
    have huc : _root_.UnitaryCollinear Θ f :=
      (theorem9_absolute_feasible_bound_rigidity f hq Θ hfeas).mp hH
    exact unitary_collinear_implies_group_isotope f hq ⟨Θ, huc⟩
  · intro hgi
    obtain ⟨Θ_opt, huc⟩ := lemma14_group_isotope_admits_unitary_collinear f hq hgi
    refine ⟨Θ_opt, huc.feasible, ?_⟩
    -- objective.re = 3n² for UC
    show (_root_.objective Θ_opt f).re = 3 * (n : ℝ) ^ 2
    exact uc_objective_value Θ_opt f huc

/-! ## Status: scaffold

The coercivity bounds split into roughly three sub-modules:

### 1. Hessian analysis (~600-800 lines)
At an optimal point `Θ_opt` (with `H(Θ_opt) = 3n²`), compute the
Hessian `∇²H(Θ_opt)` and show it's positive semidefinite, with kernel
exactly the gauge orbit (rotations + simultaneous unitary
conjugations). Bounds on the smallest non-zero eigenvalue control
coercivity.

### 2. Coefficient graph (~400-600 lines)
The "coefficient graph" `G_f` is a graph on `Fin n × Fin n × Fin n`
with edges weighted by the structure tensor. The Laplacian of `G_f`
controls how the trace identities propagate gauge variations. Mathlib
has `SimpleGraph.Laplacian` and spectral results.

### 3. Coercivity inequality (~500-1100 lines)
Combines (1) and (2) to prove the quadratic lower bound
`ℋ(Θ) - 3n² ≥ c · dist(Θ, gauge_orbit(Θ_opt))²`. Uses the Cauchy-Schwarz
+ rearrangement inequality structure inside `H`'s definition.

This is a significant project requiring substantial Mathlib analysis
and graph-theoretic infrastructure. Best approached after Tier 3A.
-/

end Coercivity

end
