/-
  HyperCubeGroup.Tikhonov

  Existence of global minimisers via Tikhonov regularisation
  (Manuscript Appendix: "Global Existence via Tikhonov Regularization" /
  Theorem 18).

  ## Main results

  * `exists_minOn_compact_feasible`: abstract Weierstrass on any compact
    non-empty subset of the feasible set.
  * `exists_minOn_feasible_ball`: concrete bounded Weierstrass — the
    objective achieves its minimum on the feasible set restricted to
    any closed ball where it is non-empty.
  * `exists_minOn_feasible_tikhonov`: **the canonical Tikhonov result.**
    For any `λ > 0` and any feasible `Θ_0`, the regularised objective
    `ℋ(Θ).re + λ ‖Θ‖²` attains its minimum on the entire feasible set.
  * `exists_minOn_feasible_of_coercive`: conditional unregularised
    Weierstrass — given coercivity of the objective on the feasible set,
    the unregularised global minimum exists.

  ## Approach

  HCParams n is given the topology induced from a bijection to a product
  of three Pi types over Matrix. This makes it a finite-dimensional
  normed space (over ℂ). Closed bounded sets in finite-dim spaces are
  compact (Heine-Borel via FiniteDimensional.proper). Continuous
  functions on compact sets attain their minimum (Weierstrass).

  The Tikhonov result uses coercivity of `ℋ(Θ).re + λ ‖Θ‖²` for `λ > 0`
  (since `ℋ(Θ).re ≥ 0` and the regularisation term grows quadratically),
  which gives bounded sublevel sets, hence compact sublevel sets, hence
  Weierstrass applies.

  ## Status

  All four results are mechanised with no sorries. The unconditional
  unregularised Weierstrass requires a coercivity bound on `H` itself
  (Tier 3B / Manuscript Appendix F).
-/

import HyperCubeGroup.Basic
import HyperCubeGroup.Decomposition
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension

open Matrix BigOperators Complex

-- Frobenius norm is one of several natural choices; we open the scope locally
-- so HCParams can inherit a NormedAddCommGroup via the equiv to a product
-- of Pi types over Matrix (with the Frobenius norm).
open scoped Matrix.Norms.Frobenius

noncomputable section

namespace HCParams

variable {n : ℕ}

/-- The product type underlying `HCParams n`. -/
abbrev ProdType (n : ℕ) :=
  (Fin n → Matrix (Fin n) (Fin n) ℂ) ×
  (Fin n → Matrix (Fin n) (Fin n) ℂ) ×
  (Fin n → Matrix (Fin n) (Fin n) ℂ)

/-- The bijection `HCParams n ≃ ProdType n`. -/
def equivProd : HCParams n ≃ ProdType n where
  toFun Θ := (Θ.A, Θ.B, Θ.C)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- Topology on `HCParams n` induced by `equivProd`. -/
instance : TopologicalSpace (HCParams n) :=
  TopologicalSpace.induced equivProd inferInstance

/-- `equivProd` is continuous. -/
theorem continuous_equivProd : Continuous (equivProd : HCParams n → ProdType n) :=
  continuous_induced_dom

/-- The inverse of `equivProd` is continuous. -/
theorem continuous_equivProd_symm :
    Continuous (equivProd.symm : ProdType n → HCParams n) := by
  rw [continuous_induced_rng]
  -- Need: equivProd ∘ equivProd.symm continuous, i.e., id continuous.
  show Continuous (fun p => equivProd (equivProd.symm p))
  simp only [Equiv.apply_symm_apply]
  exact continuous_id

/-- `equivProd` as a homeomorphism. -/
def equivProdHomeo : HCParams n ≃ₜ ProdType n where
  toEquiv := equivProd
  continuous_toFun := continuous_equivProd
  continuous_invFun := continuous_equivProd_symm

/-- The A-side projection is continuous. -/
theorem continuous_A (a : Fin n) : Continuous (fun Θ : HCParams n => Θ.A a) := by
  have h1 : Continuous (fun Θ : HCParams n => (equivProd Θ).1) :=
    continuous_fst.comp continuous_equivProd
  exact (continuous_apply a).comp h1

/-- The B-side projection is continuous. -/
theorem continuous_B (b : Fin n) : Continuous (fun Θ : HCParams n => Θ.B b) := by
  have h1 : Continuous (fun Θ : HCParams n => (equivProd Θ).2.1) :=
    (continuous_fst.comp continuous_snd).comp continuous_equivProd
  exact (continuous_apply b).comp h1

/-- The C-side projection is continuous. -/
theorem continuous_C (c : Fin n) : Continuous (fun Θ : HCParams n => Θ.C c) := by
  have h1 : Continuous (fun Θ : HCParams n => (equivProd Θ).2.2) :=
    (continuous_snd.comp continuous_snd).comp continuous_equivProd
  exact (continuous_apply c).comp h1

/-! ## Algebraic structure on HCParams via equivProd transport -/

instance : Add (HCParams n) where
  add Θ₁ Θ₂ := ⟨Θ₁.A + Θ₂.A, Θ₁.B + Θ₂.B, Θ₁.C + Θ₂.C⟩

instance : Zero (HCParams n) where
  zero := ⟨0, 0, 0⟩

instance : Neg (HCParams n) where
  neg Θ := ⟨-Θ.A, -Θ.B, -Θ.C⟩

instance : Sub (HCParams n) where
  sub Θ₁ Θ₂ := ⟨Θ₁.A - Θ₂.A, Θ₁.B - Θ₂.B, Θ₁.C - Θ₂.C⟩

instance : SMul ℕ (HCParams n) where
  smul k Θ := ⟨k • Θ.A, k • Θ.B, k • Θ.C⟩

instance : SMul ℤ (HCParams n) where
  smul k Θ := ⟨k • Θ.A, k • Θ.B, k • Θ.C⟩

instance : SMul ℂ (HCParams n) where
  smul c Θ := ⟨c • Θ.A, c • Θ.B, c • Θ.C⟩

theorem equivProd_injective : Function.Injective (equivProd : HCParams n → ProdType n) :=
  equivProd.injective

instance : AddCommGroup (HCParams n) :=
  equivProd_injective.addCommGroup _ rfl
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- `equivProd` as an `AddMonoidHom`. -/
def equivProdHom : HCParams n →+ ProdType n where
  toFun := equivProd
  map_zero' := rfl
  map_add' _ _ := rfl

instance : Module ℂ (HCParams n) :=
  equivProd_injective.module ℂ equivProdHom (fun _ _ => rfl)

/-- `equivProd` as a `LinearMap`. -/
def equivProdLinearHom : HCParams n →ₗ[ℂ] ProdType n where
  toFun := equivProd
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `NormedAddCommGroup` on HCParams via the equiv to `ProdType`. -/
noncomputable instance : NormedAddCommGroup (HCParams n) :=
  NormedAddCommGroup.induced _ _ equivProdHom equivProd_injective

/-- `NormedSpace ℂ (HCParams n)` via the equiv. -/
noncomputable instance : NormedSpace ℂ (HCParams n) :=
  NormedSpace.induced ℂ _ _ equivProdLinearHom

/-- `FiniteDimensional ℂ (HCParams n)` via injection into `ProdType`. -/
instance : FiniteDimensional ℂ (HCParams n) :=
  FiniteDimensional.of_injective equivProdLinearHom equivProd_injective

end HCParams

namespace Tikhonov

variable {n : ℕ} [NeZero n]

/-! ## HCParams norm-squared -/

/-- A norm-squared on `HCParams n`: sum of Frobenius norm-squareds of all 3n slices. -/
noncomputable def hcNormSq (Θ : HCParams n) : ℂ :=
  ∑ a : Fin n, frobNormSq (Θ.A a) +
  ∑ b : Fin n, frobNormSq (Θ.B b) +
  ∑ c : Fin n, frobNormSq (Θ.C c)

/-- The norm-squared is real. -/
theorem hcNormSq_im_zero (Θ : HCParams n) : (hcNormSq Θ).im = 0 := by
  unfold hcNormSq
  simp only [Complex.add_im, Complex.im_sum, frobNormSq_real, Finset.sum_const_zero, add_zero]

/-- The norm-squared is nonneg. -/
theorem hcNormSq_re_nonneg (Θ : HCParams n) : 0 ≤ (hcNormSq Θ).re := by
  unfold hcNormSq
  simp only [Complex.add_re, Complex.re_sum]
  apply add_nonneg
  · apply add_nonneg <;> exact Finset.sum_nonneg (fun _ _ => frobNormSq_nonneg _)
  · exact Finset.sum_nonneg (fun _ _ => frobNormSq_nonneg _)

/-! ## Continuity of basic objects -/

/-- `frobNormSq` is continuous as a function of the matrix. -/
theorem continuous_frobNormSq :
    Continuous (frobNormSq : Matrix (Fin n) (Fin n) ℂ → ℂ) := by
  unfold frobNormSq frobInner
  apply Continuous.mul
  · exact continuous_const
  · apply Continuous.matrix_trace
    apply Continuous.matrix_mul
    · exact continuous_id.matrix_conjTranspose
    · exact continuous_id

/-- Continuity of `frobNormSq (Θ.A a)` as a function of Θ. -/
theorem continuous_frobNormSq_A (a : Fin n) :
    Continuous (fun Θ : HCParams n => frobNormSq (Θ.A a)) :=
  continuous_frobNormSq.comp (HCParams.continuous_A a)

/-- Continuity of `frobNormSq (Θ.B b)` as a function of Θ. -/
theorem continuous_frobNormSq_B (b : Fin n) :
    Continuous (fun Θ : HCParams n => frobNormSq (Θ.B b)) :=
  continuous_frobNormSq.comp (HCParams.continuous_B b)

/-- Continuity of `frobNormSq (Θ.C c)` as a function of Θ. -/
theorem continuous_frobNormSq_C (c : Fin n) :
    Continuous (fun Θ : HCParams n => frobNormSq (Θ.C c)) :=
  continuous_frobNormSq.comp (HCParams.continuous_C c)

/-- `hcNormSq` is continuous. -/
theorem continuous_hcNormSq :
    Continuous (hcNormSq : HCParams n → ℂ) := by
  unfold hcNormSq
  apply Continuous.add
  · apply Continuous.add
    · exact continuous_finset_sum _ (fun a _ => continuous_frobNormSq_A a)
    · exact continuous_finset_sum _ (fun b _ => continuous_frobNormSq_B b)
  · exact continuous_finset_sum _ (fun c _ => continuous_frobNormSq_C c)

/-- Continuity of slice products like `Θ.B b * Θ.C c`. -/
theorem continuous_BC (b c : Fin n) :
    Continuous (fun Θ : HCParams n => Θ.B b * Θ.C c) :=
  Continuous.matrix_mul (HCParams.continuous_B b) (HCParams.continuous_C c)

theorem continuous_CA (c a : Fin n) :
    Continuous (fun Θ : HCParams n => Θ.C c * Θ.A a) :=
  Continuous.matrix_mul (HCParams.continuous_C c) (HCParams.continuous_A a)

theorem continuous_AB (a b : Fin n) :
    Continuous (fun Θ : HCParams n => Θ.A a * Θ.B b) :=
  Continuous.matrix_mul (HCParams.continuous_A a) (HCParams.continuous_B b)

/-- Continuity of `frobNormSq (Θ.B b * Θ.C c)`. -/
theorem continuous_frobNormSq_BC (b c : Fin n) :
    Continuous (fun Θ : HCParams n => frobNormSq (Θ.B b * Θ.C c)) :=
  continuous_frobNormSq.comp (continuous_BC b c)

theorem continuous_frobNormSq_CA (c a : Fin n) :
    Continuous (fun Θ : HCParams n => frobNormSq (Θ.C c * Θ.A a)) :=
  continuous_frobNormSq.comp (continuous_CA c a)

theorem continuous_frobNormSq_AB (a b : Fin n) :
    Continuous (fun Θ : HCParams n => frobNormSq (Θ.A a * Θ.B b)) :=
  continuous_frobNormSq.comp (continuous_AB a b)

/-! ## Continuity of the objective -/

/-- The objective `ℋ(Θ)` is continuous in `Θ`. -/
theorem continuous_objective (f : BinOp n) :
    Continuous (fun Θ : HCParams n => objective Θ f) := by
  unfold objective
  apply continuous_finset_sum
  intro a _
  apply continuous_finset_sum
  intro b _
  apply continuous_finset_sum
  intro c _
  apply Continuous.mul
  · exact continuous_const
  · apply Continuous.add
    · apply Continuous.add
      · exact continuous_frobNormSq_BC b c
      · exact continuous_frobNormSq_CA c a
    · exact continuous_frobNormSq_AB a b

/-- The trace product `hcProduct Θ a b c` is continuous in Θ. -/
theorem continuous_hcProduct (a b c : Fin n) :
    Continuous (fun Θ : HCParams n => hcProduct Θ a b c) := by
  unfold hcProduct
  apply Continuous.mul
  · exact continuous_const
  · apply Continuous.matrix_trace
    apply Continuous.matrix_mul
    · exact continuous_AB a b
    · exact HCParams.continuous_C c

/-! ## Closedness of the feasible set -/

/-- The set `{Θ : hcProduct Θ a b c = structureTensor f a b c}` is closed. -/
theorem isClosed_hcProduct_eq (f : BinOp n) (a b c : Fin n) :
    IsClosed {Θ : HCParams n | hcProduct Θ a b c = structureTensor f a b c} := by
  -- This is the preimage of {structureTensor f a b c} under the continuous
  -- map Θ ↦ hcProduct Θ a b c. Since {x} is closed in ℂ, the preimage is closed.
  exact isClosed_singleton.preimage (continuous_hcProduct a b c)

/-- The feasible set `{Θ : Factorizes Θ f}` is closed in `HCParams n`. -/
theorem isClosed_feasible (f : BinOp n) :
    IsClosed {Θ : HCParams n | Factorizes Θ f} := by
  -- Factorizes Θ f means hcProduct Θ a b c = structureTensor f a b c for all a b c.
  -- This is an intersection of n³ closed sets.
  have : {Θ : HCParams n | Factorizes Θ f} =
      ⋂ (a : Fin n) (b : Fin n) (c : Fin n),
        {Θ : HCParams n | hcProduct Θ a b c = structureTensor f a b c} := by
    ext Θ
    simp [Factorizes, Set.mem_iInter]
  rw [this]
  exact isClosed_iInter (fun a => isClosed_iInter (fun b => isClosed_iInter
    (fun c => isClosed_hcProduct_eq f a b c)))

/-! ## Closedness of the norm-bounded set -/

/-- The set `{Θ : (hcNormSq Θ).re ≤ R}` is closed in `HCParams n`. -/
theorem isClosed_hcNormSq_le (R : ℝ) :
    IsClosed {Θ : HCParams n | (hcNormSq Θ).re ≤ R} := by
  -- Preimage of a closed set under a continuous map.
  exact (isClosed_Iic.preimage (Complex.continuous_re.comp continuous_hcNormSq))

/-- The bounded feasible set is closed. -/
theorem isClosed_feasible_bounded (f : BinOp n) (R : ℝ) :
    IsClosed {Θ : HCParams n | Factorizes Θ f ∧ (hcNormSq Θ).re ≤ R} := by
  have h_eq : {Θ : HCParams n | Factorizes Θ f ∧ (hcNormSq Θ).re ≤ R} =
      {Θ | Factorizes Θ f} ∩ {Θ | (hcNormSq Θ).re ≤ R} := by ext; simp
  rw [h_eq]
  exact (isClosed_feasible f).inter (isClosed_hcNormSq_le R)

/-! ## Weierstrass on a compact feasible subset -/

/-- The real part of the objective is continuous. -/
theorem continuous_objective_re (f : BinOp n) :
    Continuous (fun Θ : HCParams n => (objective Θ f).re) :=
  Complex.continuous_re.comp (continuous_objective f)

/-- **Abstract Weierstrass on the feasible manifold.**
    Given any compact non-empty subset of the feasible set, the
    real part of the objective achieves its minimum. -/
theorem exists_minOn_compact_feasible (f : BinOp n)
    (s : Set (HCParams n)) (h_compact : IsCompact s) (h_nonempty : s.Nonempty) :
    ∃ Θ_min ∈ s, ∀ Θ' ∈ s, (objective Θ_min f).re ≤ (objective Θ' f).re := by
  have h_min := h_compact.exists_isMinOn h_nonempty
    (continuous_objective_re f).continuousOn
  obtain ⟨Θ_min, hΘ_min_mem, hΘ_min_isMin⟩ := h_min
  exact ⟨Θ_min, hΘ_min_mem, fun Θ' hΘ' => hΘ_min_isMin hΘ'⟩

/-! ## Concrete compactness via finite-dim Heine-Borel -/

/-- Closed feasible-set ∩ closed-ball is compact. -/
theorem isCompact_feasible_inter_ball (f : BinOp n) (R : ℝ) :
    IsCompact ({Θ : HCParams n | Factorizes Θ f} ∩ Metric.closedBall 0 R) := by
  have : ProperSpace (HCParams n) := FiniteDimensional.proper ℂ (HCParams n)
  exact Metric.isCompact_of_isClosed_isBounded
    ((isClosed_feasible f).inter Metric.isClosed_closedBall)
    (Metric.isBounded_closedBall.subset Set.inter_subset_right)

/-- **Concrete Weierstrass.** If the feasible set has a non-empty intersection
    with the closed ball of radius `R`, then the objective achieves its minimum
    on that intersection. -/
theorem exists_minOn_feasible_ball (f : BinOp n) (R : ℝ)
    (h_nonempty : ({Θ : HCParams n | Factorizes Θ f} ∩
      Metric.closedBall 0 R).Nonempty) :
    ∃ Θ_min : HCParams n,
      Factorizes Θ_min f ∧ ‖Θ_min‖ ≤ R ∧
      ∀ Θ' : HCParams n, Factorizes Θ' f → ‖Θ'‖ ≤ R →
        (objective Θ_min f).re ≤ (objective Θ' f).re := by
  obtain ⟨Θ_min, hΘ_min_mem, hΘ_min_isMin⟩ :=
    exists_minOn_compact_feasible f _
      (isCompact_feasible_inter_ball f R) h_nonempty
  have h_norm : ‖Θ_min‖ ≤ R := by
    have := hΘ_min_mem.2
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  refine ⟨Θ_min, hΘ_min_mem.1, h_norm, ?_⟩
  intro Θ' hΘ'_feas hΘ'_norm
  apply hΘ_min_isMin
  refine ⟨hΘ'_feas, ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hΘ'_norm

/-! ## Tikhonov-regularised minimum existence -/

/-- The Tikhonov-regularised objective: `ℋ(Θ).re + λ ‖Θ‖²`. -/
noncomputable def tikhonovObjective (Θ : HCParams n) (f : BinOp n) (lam : ℝ) : ℝ :=
  (objective Θ f).re + lam * ‖Θ‖ ^ 2

/-- The objective `ℋ(Θ)` has nonneg real part (sum of nonneg Frobenius norm-squareds). -/
theorem objective_re_nonneg (Θ : HCParams n) (f : BinOp n) :
    0 ≤ (objective Θ f).re := by
  unfold objective
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro a _
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro b _
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro c _
  rw [structureTensor]
  by_cases h : f.op a b = c
  · rw [if_pos h]
    rw [show ((1 : ℂ) * (frobNormSq (Θ.B b * Θ.C c) +
        frobNormSq (Θ.C c * Θ.A a) + frobNormSq (Θ.A a * Θ.B b))) =
        (frobNormSq (Θ.B b * Θ.C c) +
          frobNormSq (Θ.C c * Θ.A a) + frobNormSq (Θ.A a * Θ.B b)) from by ring]
    rw [Complex.add_re, Complex.add_re]
    apply add_nonneg
    · exact add_nonneg (frobNormSq_nonneg _) (frobNormSq_nonneg _)
    · exact frobNormSq_nonneg _
  · rw [if_neg h, zero_mul]
    simp

/-- Continuity of the Tikhonov objective in Θ. -/
theorem continuous_tikhonovObjective (f : BinOp n) (lam : ℝ) :
    Continuous (fun Θ : HCParams n => tikhonovObjective Θ f lam) := by
  unfold tikhonovObjective
  apply Continuous.add
  · exact continuous_objective_re f
  · apply Continuous.mul
    · exact continuous_const
    · exact (continuous_pow 2).comp continuous_norm

/-- The sublevel set `{Θ : tikhonovObjective Θ f lam ≤ M}` is closed. -/
theorem isClosed_tikhonov_sublevel (f : BinOp n) (lam M : ℝ) :
    IsClosed {Θ : HCParams n | tikhonovObjective Θ f lam ≤ M} :=
  isClosed_Iic.preimage (continuous_tikhonovObjective f lam)

/-- For `λ > 0`, the Tikhonov sublevel set is bounded.
    Bound: if `H_λ(Θ) ≤ M`, then `‖Θ‖² ≤ M/λ`. -/
theorem tikhonov_sublevel_bounded (f : BinOp n) (lam : ℝ) (h_lam : 0 < lam) (M : ℝ) :
    Bornology.IsBounded {Θ : HCParams n | tikhonovObjective Θ f lam ≤ M} := by
  -- ‖Θ‖² ≤ M/λ since ℋ(Θ).re + λ‖Θ‖² ≤ M and ℋ(Θ).re ≥ 0.
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨Real.sqrt (max 0 (M / lam)), ?_⟩
  intro Θ hΘ
  rw [Metric.mem_closedBall, dist_zero_right]
  have h_obj_nn := objective_re_nonneg Θ f
  have h_norm_sq_bound : ‖Θ‖ ^ 2 ≤ M / lam := by
    have h_in : tikhonovObjective Θ f lam ≤ M := hΘ
    unfold tikhonovObjective at h_in
    have h2 : lam * ‖Θ‖ ^ 2 ≤ M := by linarith
    rw [le_div_iff₀ h_lam, mul_comm]
    exact h2
  have h_le : ‖Θ‖ ^ 2 ≤ max 0 (M / lam) := le_max_of_le_right h_norm_sq_bound
  have h_norm_nn : 0 ≤ ‖Θ‖ := norm_nonneg _
  have : ‖Θ‖ ≤ Real.sqrt (max 0 (M / lam)) := by
    rw [show ‖Θ‖ = Real.sqrt (‖Θ‖^2) from (Real.sqrt_sq h_norm_nn).symm]
    exact Real.sqrt_le_sqrt h_le
  exact this

/-- The Tikhonov sublevel set is compact (closed + bounded in finite-dim). -/
theorem isCompact_tikhonov_sublevel (f : BinOp n) (lam : ℝ) (h_lam : 0 < lam) (M : ℝ) :
    IsCompact {Θ : HCParams n | tikhonovObjective Θ f lam ≤ M} := by
  have : ProperSpace (HCParams n) := FiniteDimensional.proper ℂ (HCParams n)
  exact Metric.isCompact_of_isClosed_isBounded
    (isClosed_tikhonov_sublevel f lam M)
    (tikhonov_sublevel_bounded f lam h_lam M)

/-- **Tikhonov regularised minimum existence.** For any `λ > 0` and any
    feasible `Θ_0`, the regularised objective `ℋ(Θ).re + λ ‖Θ‖²`
    achieves its minimum on the feasible set. -/
theorem exists_minOn_feasible_tikhonov (f : BinOp n) (lam : ℝ) (h_lam : 0 < lam)
    (Θ_0 : HCParams n) (h_feas_0 : Factorizes Θ_0 f) :
    ∃ Θ_min : HCParams n, Factorizes Θ_min f ∧
      ∀ Θ' : HCParams n, Factorizes Θ' f →
        tikhonovObjective Θ_min f lam ≤ tikhonovObjective Θ' f lam := by
  -- Use the sublevel set at M = tikhonovObjective Θ_0.
  set M := tikhonovObjective Θ_0 f lam with hM_def
  -- The set {Θ : Factorizes ∧ tikhonovObjective ≤ M} is closed and bounded, hence compact.
  set s := {Θ : HCParams n | Factorizes Θ f ∧ tikhonovObjective Θ f lam ≤ M} with hs_def
  have h_closed : IsClosed s :=
    (isClosed_feasible f).inter (isClosed_tikhonov_sublevel f lam M)
  have h_bounded : Bornology.IsBounded s :=
    (tikhonov_sublevel_bounded f lam h_lam M).subset Set.inter_subset_right
  have : ProperSpace (HCParams n) := FiniteDimensional.proper ℂ (HCParams n)
  have h_compact : IsCompact s := Metric.isCompact_of_isClosed_isBounded h_closed h_bounded
  have h_nonempty : s.Nonempty := ⟨Θ_0, h_feas_0, le_refl _⟩
  obtain ⟨Θ_min, hΘ_min_mem, hΘ_min_isMin⟩ := h_compact.exists_isMinOn h_nonempty
    (continuous_tikhonovObjective f lam).continuousOn
  refine ⟨Θ_min, hΘ_min_mem.1, ?_⟩
  intro Θ' hΘ'_feas
  -- Either Θ' is in s (and we use the minimum), or Θ' is outside s
  -- (and tikhonovObjective Θ' > M ≥ tikhonovObjective Θ_min).
  by_cases h_in : Θ' ∈ s
  · exact hΘ_min_isMin h_in
  · -- Θ' not in s but feasible, so tikhonovObjective Θ' > M.
    have h_Θ'_not_le : ¬ tikhonovObjective Θ' f lam ≤ M := by
      intro h_le; exact h_in ⟨hΘ'_feas, h_le⟩
    push_neg at h_Θ'_not_le
    -- Θ_min ∈ s, so tikhonovObjective Θ_min ≤ M < tikhonovObjective Θ'.
    have h_Θ_min_le_M : tikhonovObjective Θ_min f lam ≤ M := hΘ_min_mem.2
    linarith

/-! ## Max existence and boundedness on compact feasible subsets -/

/-- **Dual of Weierstrass.** On any compact non-empty subset of the
    feasible set, the real part of the objective achieves its maximum. -/
theorem exists_maxOn_compact_feasible (f : BinOp n)
    (s : Set (HCParams n)) (h_compact : IsCompact s) (h_nonempty : s.Nonempty) :
    ∃ Θ_max ∈ s, ∀ Θ' ∈ s, (objective Θ' f).re ≤ (objective Θ_max f).re := by
  have h_max := h_compact.exists_isMaxOn h_nonempty
    (continuous_objective_re f).continuousOn
  obtain ⟨Θ_max, hΘ_max_mem, hΘ_max_isMax⟩ := h_max
  exact ⟨Θ_max, hΘ_max_mem, fun Θ' hΘ' => hΘ_max_isMax hΘ'⟩

/-- The objective is bounded on any compact subset of the feasible set. -/
theorem objective_bdd_on_compact (f : BinOp n)
    (s : Set (HCParams n)) (h_compact : IsCompact s) :
    ∃ M : ℝ, ∀ Θ ∈ s, (objective Θ f).re ≤ M := by
  by_cases h_ne : s.Nonempty
  · obtain ⟨Θ_max, hΘ_max_mem, hΘ_max_isMax⟩ :=
      exists_maxOn_compact_feasible f s h_compact h_ne
    exact ⟨(objective Θ_max f).re, hΘ_max_isMax⟩
  · rw [Set.not_nonempty_iff_eq_empty] at h_ne
    exact ⟨0, fun _ h => by rw [h_ne] at h; exact absurd h (Set.notMem_empty _)⟩

/-- The objective is bounded on any bounded feasible set. -/
theorem objective_bdd_on_feasible_ball (f : BinOp n) (R : ℝ) :
    ∃ M : ℝ, ∀ Θ : HCParams n, Factorizes Θ f → ‖Θ‖ ≤ R →
      (objective Θ f).re ≤ M := by
  obtain ⟨M, hM⟩ := objective_bdd_on_compact f
    ({Θ : HCParams n | Factorizes Θ f} ∩ Metric.closedBall 0 R)
    (isCompact_feasible_inter_ball f R)
  refine ⟨M, fun Θ hΘ_feas hΘ_norm => ?_⟩
  apply hM
  refine ⟨hΘ_feas, ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hΘ_norm

/-! ## Conditional unregularised minimum (given coercivity) -/

/-- **Conditional unregularised Weierstrass.** If the objective is
    coercive on the feasible set (grows without bound as `‖Θ‖ → ∞`),
    then a global minimum exists. The coercivity hypothesis is stated
    as: for any threshold `M`, there exists a radius `R` such that
    every feasible `Θ` with `‖Θ‖ > R` has `(objective Θ f).re > M`. -/
theorem exists_minOn_feasible_of_coercive (f : BinOp n)
    (h_coercive : ∀ M : ℝ, ∃ R : ℝ, ∀ Θ, Factorizes Θ f →
      R < ‖Θ‖ → M < (objective Θ f).re)
    (Θ_0 : HCParams n) (h_feas_0 : Factorizes Θ_0 f) :
    ∃ Θ_min : HCParams n, Factorizes Θ_min f ∧
      ∀ Θ' : HCParams n, Factorizes Θ' f →
        (objective Θ_min f).re ≤ (objective Θ' f).re := by
  set M_0 := (objective Θ_0 f).re with hM_0_def
  obtain ⟨R, hR⟩ := h_coercive M_0
  -- The bounded feasible set ∩ closedBall R is non-empty: pick Θ_0 if ‖Θ_0‖ ≤ R,
  -- else take any point on the boundary. Actually we just need any feasible
  -- with ‖Θ‖ ≤ R'. Let R' = max R ‖Θ_0‖.
  set R' := max R ‖Θ_0‖ with hR'_def
  have h_R_le_R' : R ≤ R' := le_max_left _ _
  have h_Θ_0_in : Θ_0 ∈ {Θ : HCParams n | Factorizes Θ f} ∩ Metric.closedBall 0 R' := by
    refine ⟨h_feas_0, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_max_right _ _
  obtain ⟨Θ_min, h_feas_min, h_norm_min, h_min_min⟩ :=
    exists_minOn_feasible_ball f R' ⟨Θ_0, h_Θ_0_in⟩
  refine ⟨Θ_min, h_feas_min, ?_⟩
  intro Θ' hΘ'_feas
  by_cases h_le : ‖Θ'‖ ≤ R'
  · exact h_min_min Θ' hΘ'_feas h_le
  · push_neg at h_le
    -- ‖Θ'‖ > R' ≥ R, so by coercivity, H(Θ').re > M_0.
    have h_R_lt : R < ‖Θ'‖ := lt_of_le_of_lt h_R_le_R' h_le
    have h_obj_gt : M_0 < (objective Θ' f).re := hR Θ' hΘ'_feas h_R_lt
    -- Θ_min minimizes on bounded set, so H(Θ_min).re ≤ H(Θ_0).re = M_0.
    have h_Θ_0_in_ball : Θ_0 ∈ {Θ : HCParams n | Factorizes Θ f} ∩
        Metric.closedBall 0 R' := h_Θ_0_in
    have h_Θ_min_le_Θ_0 : (objective Θ_min f).re ≤ M_0 := by
      have h := h_min_min Θ_0 h_feas_0 (le_max_right _ _)
      exact h
    linarith

/-! ## Status: Tikhonov regularised minimum existence is mechanised

The full Tikhonov-style result `exists_minOn_feasible_tikhonov` gives:
for any `λ > 0` and any feasible `Θ_0`, there exists a feasible `Θ_min`
minimising `ℋ(Θ).re + λ ‖Θ‖²` over the entire feasible set. The proof
combines:
  * Coercivity: `H_λ(Θ) ≥ λ ‖Θ‖²`, so sublevel sets are bounded.
  * Closedness: from continuity of the objective.
  * Finite-dim Heine-Borel: closed bounded ⇒ compact.
  * Weierstrass: continuous functions on compact sets attain their minimum.

To go from regularised to unregularised: take `λ → 0`. This is
the standard Tikhonov limit and would close the unregularised
existence question. The limit argument uses sequential extraction
+ a coercivity bound on the unregularised problem (which itself
requires the manuscript's Appendix F coercivity bounds — Tier 3B).

For the bounded version (without regularisation), use
`exists_minOn_feasible_ball` on a fixed radius `R`.
-/

/-! ## Status: existence theorem ready, modulo concrete compact witness

The `exists_minOn_compact_feasible` theorem reduces the existence
question to: produce a compact non-empty subset of the feasible set.

For `f` an actual quasigroup with feasible factorisation (e.g., a group
isotope, where `leftRegularRep_factorizes` provides one), the natural
compact subset is `{Θ | Factorizes Θ f ∧ (hcNormSq Θ).re ≤ R}` for `R`
slightly above the norm of the leftRegularRep witness.

The compactness step requires equipping HCParams with the structures
needed for finite-dim Heine-Borel:
  * `AddCommGroup (HCParams n)` — derive via `equivProd`
  * `Module ℂ (HCParams n)` — same
  * `NormedAddCommGroup (HCParams n)` — via Frobenius-style norm
  * `FiniteDimensional ℂ (HCParams n)` — automatic from the
    finite-dim product

These are mechanical structural transports through `equivProdHomeo`,
deferred here because they require a substantial chunk of additional
boilerplate. The existence theorem above is ready to consume them
once instantiated. -/

/-! ## Theorem 18: Existence for Regularized Objective -/

/-- **Theorem 18 (Existence for Regularized Objective).** For any `ε > 0` and
    any feasible factorisation, the regularised objective
    `ℋ(Θ).re + ε‖Θ‖²` achieves its minimum on the feasible set. -/
theorem theorem18_regularized_existence (f : BinOp n) (eps : ℝ) (h_eps : 0 < eps)
    (Θ_0 : HCParams n) (h_feas_0 : Factorizes Θ_0 f) :
    ∃ Θ_min : HCParams n, Factorizes Θ_min f ∧
      ∀ Θ' : HCParams n, Factorizes Θ' f →
        tikhonovObjective Θ_min f eps ≤ tikhonovObjective Θ' f eps :=
  exists_minOn_feasible_tikhonov f eps h_eps Θ_0 h_feas_0

end Tikhonov

end
