/-
  HyperCubeGroup.BlockCyclic

  The 3n × 3n block-cyclic matrix
    M = [[0, X, 0],
         [0, 0, Y],
         [Z, 0, 0]]
  built from `(X, Y, Z) ∈ (Mat n)³`, used in the matrix AM-GM proof
  (App_Abelian_Dominance.tex §2). We index by `Fin 3 × Fin n` rather
  than via `Matrix.fromBlocks` (which is 2×2), to keep the entry-wise
  computations self-contained.

  Main outputs:

    * `blockCyclic` — definition.
    * `blockCyclic_sq_apply` — explicit M² entries (block (XY,YZ,ZX)).
    * `blockCyclic_cb_apply` — explicit M³ entries (block diag XYZ etc).
    * `frobNormSq_F_blockCyclic_sq` — `‖M²‖²_F = ‖XY‖²_F + ‖YZ‖²_F + ‖ZX‖²_F`.
    * `trace_blockCyclic_cb` — `Tr(M³) = 3 · Tr(XYZ)`.
-/

import HyperCubeGroup.Spectral
import Mathlib.Logic.Equiv.Fin.Basic

open Matrix BigOperators Complex

noncomputable section

variable {n : ℕ}

/-- The 3n × 3n block-cyclic matrix from `(X, Y, Z)`. Indexed by
    `Fin 3 × Fin n`. Block `(0, 1)` is `X`, block `(1, 2)` is `Y`,
    block `(2, 0)` is `Z`; all other blocks are zero. -/
def blockCyclic (X Y Z : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ :=
  fun ⟨i, p⟩ ⟨j, q⟩ =>
    if i.val = 0 ∧ j.val = 1 then X p q
    else if i.val = 1 ∧ j.val = 2 then Y p q
    else if i.val = 2 ∧ j.val = 0 then Z p q
    else 0

/-- Explicit form of `M · M` when `M = blockCyclic X Y Z`: nonzero
    blocks are `XY`, `YZ`, `ZX` at positions `(0,2)`, `(1,0)`, `(2,1)`. -/
def blockCyclicSq (X Y Z : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ :=
  fun ⟨i, p⟩ ⟨k, r⟩ =>
    if i.val = 0 ∧ k.val = 2 then (X * Y) p r
    else if i.val = 1 ∧ k.val = 0 then (Y * Z) p r
    else if i.val = 2 ∧ k.val = 1 then (Z * X) p r
    else 0

/-- Entry-wise computation of `(M · M) (i, p) (k, r)` for the
    block-cyclic `M`. -/
theorem blockCyclic_mul_self (X Y Z : Matrix (Fin n) (Fin n) ℂ) :
    blockCyclic X Y Z * blockCyclic X Y Z = blockCyclicSq X Y Z := by
  ext ⟨i, p⟩ ⟨k, r⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_three]
  -- Σ_q M(i,p)(0,q)·M(0,q)(k,r) + Σ_q M(i,p)(1,q)·M(1,q)(k,r) + Σ_q M(i,p)(2,q)·M(2,q)(k,r)
  fin_cases i <;> fin_cases k <;>
    simp only [blockCyclic, blockCyclicSq,
               show ((0 : Fin 3) : ℕ) = 0 from rfl,
               show ((1 : Fin 3) : ℕ) = 1 from rfl,
               show ((2 : Fin 3) : ℕ) = 2 from rfl,
               Nat.zero_ne_one, Nat.one_ne_zero,
               (by decide : (0 : ℕ) ≠ 2), (by decide : (2 : ℕ) ≠ 0),
               (by decide : (1 : ℕ) ≠ 2), (by decide : (2 : ℕ) ≠ 1),
               and_true, true_and, and_self, ite_true, ite_false,
               and_false, false_and, if_false,
               mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add] <;>
    first
    | rfl
    | rw [← Matrix.mul_apply]; rfl

/-- `‖M²‖²_F = ‖XY‖²_F + ‖YZ‖²_F + ‖ZX‖²_F` for `M = blockCyclic X Y Z`. -/
theorem frobNormSq_F_blockCyclicSq (X Y Z : Matrix (Fin n) (Fin n) ℂ) :
    frobNormSq_F (blockCyclicSq X Y Z) =
    frobNormSq_F (X * Y) + frobNormSq_F (Y * Z) + frobNormSq_F (Z * X) := by
  unfold frobNormSq_F blockCyclicSq
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three,
             show ((0 : Fin 3) : ℕ) = 0 from rfl,
             show ((1 : Fin 3) : ℕ) = 1 from rfl,
             show ((2 : Fin 3) : ℕ) = 2 from rfl,
             Nat.zero_ne_one, Nat.one_ne_zero,
             (by decide : (0 : ℕ) ≠ 2), (by decide : (2 : ℕ) ≠ 0),
             (by decide : (1 : ℕ) ≠ 2), (by decide : (2 : ℕ) ≠ 1),
             and_true, true_and, and_self, ite_true, ite_false,
             and_false, false_and,
             Complex.normSq_zero, Finset.sum_const_zero, zero_add, add_zero]

/-- The Frobenius² of `M·M` (the block-cyclic squared) decomposes
    cyclically: `‖M·M‖²_F = ‖XY‖² + ‖YZ‖² + ‖ZX‖²`. -/
theorem frobNormSq_F_blockCyclic_sq (X Y Z : Matrix (Fin n) (Fin n) ℂ) :
    frobNormSq_F (blockCyclic X Y Z * blockCyclic X Y Z) =
    frobNormSq_F (X * Y) + frobNormSq_F (Y * Z) + frobNormSq_F (Z * X) := by
  rw [blockCyclic_mul_self, frobNormSq_F_blockCyclicSq]

/-- Explicit form of `M · M · M`: block-diagonal with blocks `XYZ, YZX,
    ZXY` at `(0,0), (1,1), (2,2)`. -/
def blockCyclicCb (X Y Z : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ :=
  fun ⟨i, p⟩ ⟨l, s⟩ =>
    if i.val = 0 ∧ l.val = 0 then (X * Y * Z) p s
    else if i.val = 1 ∧ l.val = 1 then (Y * Z * X) p s
    else if i.val = 2 ∧ l.val = 2 then (Z * X * Y) p s
    else 0

/-- Entry-wise computation of `M · M²` for the block-cyclic `M`. -/
theorem blockCyclic_mul_blockCyclicSq (X Y Z : Matrix (Fin n) (Fin n) ℂ) :
    blockCyclic X Y Z * blockCyclicSq X Y Z = blockCyclicCb X Y Z := by
  ext ⟨i, p⟩ ⟨l, s⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_three]
  fin_cases i <;> fin_cases l <;>
    simp only [blockCyclic, blockCyclicSq, blockCyclicCb,
               show ((0 : Fin 3) : ℕ) = 0 from rfl,
               show ((1 : Fin 3) : ℕ) = 1 from rfl,
               show ((2 : Fin 3) : ℕ) = 2 from rfl,
               Nat.zero_ne_one, Nat.one_ne_zero,
               (by decide : (0 : ℕ) ≠ 2), (by decide : (2 : ℕ) ≠ 0),
               (by decide : (1 : ℕ) ≠ 2), (by decide : (2 : ℕ) ≠ 1),
               and_true, true_and, and_self, ite_true, ite_false,
               and_false, false_and, if_false,
               mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add] <;>
    first
    | rfl
    | (rw [← Matrix.mul_apply, ← Matrix.mul_assoc])

/-! ## Unitarity correspondence: `blockCyclic` unitary iff `X, Y, Z` unitary -/

/-- Entry-wise form of the conjugate transpose of `blockCyclic X Y Z`.
    Block `(1, 0)` is `Xᴴ`, block `(2, 1)` is `Yᴴ`, block `(0, 2)` is `Zᴴ`. -/
theorem blockCyclic_conjTranspose_apply (X Y Z : Matrix (Fin n) (Fin n) ℂ)
    (i : Fin 3) (p : Fin n) (j : Fin 3) (q : Fin n) :
    ((blockCyclic X Y Z)ᴴ) ⟨i, p⟩ ⟨j, q⟩ =
    (if i.val = 1 ∧ j.val = 0 then (Xᴴ) p q
     else if i.val = 2 ∧ j.val = 1 then (Yᴴ) p q
     else if i.val = 0 ∧ j.val = 2 then (Zᴴ) p q
     else 0) := by
  rw [Matrix.conjTranspose_apply]
  unfold blockCyclic
  fin_cases i <;> fin_cases j <;>
    simp only [show ((0 : Fin 3) : ℕ) = 0 from rfl,
               show ((1 : Fin 3) : ℕ) = 1 from rfl,
               show ((2 : Fin 3) : ℕ) = 2 from rfl,
               and_self, and_true, true_and,
               (by decide : (0 : ℕ) ≠ 1), (by decide : (1 : ℕ) ≠ 0),
               (by decide : (0 : ℕ) ≠ 2), (by decide : (2 : ℕ) ≠ 0),
               (by decide : (1 : ℕ) ≠ 2), (by decide : (2 : ℕ) ≠ 1),
               and_false, false_and,
               ite_true, ite_false, if_true, if_false, star_zero] <;>
    rfl

/-- Entry-wise form of `M · Mᴴ` for `M = blockCyclic X Y Z`: it is
    block-diagonal with `(0,0) = X·Xᴴ`, `(1,1) = Y·Yᴴ`, `(2,2) = Z·Zᴴ`. -/
theorem blockCyclic_mul_conjTranspose_apply
    (X Y Z : Matrix (Fin n) (Fin n) ℂ)
    (i : Fin 3) (p : Fin n) (j : Fin 3) (q : Fin n) :
    (blockCyclic X Y Z * (blockCyclic X Y Z)ᴴ) ⟨i, p⟩ ⟨j, q⟩ =
    (if i.val = 0 ∧ j.val = 0 then (X * Xᴴ) p q
     else if i.val = 1 ∧ j.val = 1 then (Y * Yᴴ) p q
     else if i.val = 2 ∧ j.val = 2 then (Z * Zᴴ) p q
     else 0) := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;>
    simp only [blockCyclic, blockCyclic_conjTranspose_apply,
               show ((0 : Fin 3) : ℕ) = 0 from rfl,
               show ((1 : Fin 3) : ℕ) = 1 from rfl,
               show ((2 : Fin 3) : ℕ) = 2 from rfl,
               (by decide : (0 : ℕ) ≠ 1), (by decide : (1 : ℕ) ≠ 0),
               (by decide : (0 : ℕ) ≠ 2), (by decide : (2 : ℕ) ≠ 0),
               (by decide : (1 : ℕ) ≠ 2), (by decide : (2 : ℕ) ≠ 1),
               and_self, and_true, true_and, and_false, false_and,
               ite_true, ite_false, if_false,
               mul_zero, zero_mul, Finset.sum_const_zero,
               add_zero, zero_add] <;>
    first
    | rfl
    | rw [← Matrix.mul_apply]; rfl

/-- `blockCyclic X Y Z` is unitary (`M · Mᴴ = 1`) iff each of `X, Y, Z`
    is unitary in the same sense. -/
theorem blockCyclic_mul_conjTranspose_eq_one_iff
    (X Y Z : Matrix (Fin n) (Fin n) ℂ) :
    blockCyclic X Y Z * (blockCyclic X Y Z)ᴴ = 1 ↔
    X * Xᴴ = 1 ∧ Y * Yᴴ = 1 ∧ Z * Zᴴ = 1 := by
  classical
  -- Helper for extracting the (i, j) block from the M·Mᴴ = 1 equation.
  have extract : ∀ (i : Fin 3), blockCyclic X Y Z * (blockCyclic X Y Z)ᴴ = 1 →
      ∀ (p q : Fin n),
        (blockCyclic X Y Z * (blockCyclic X Y Z)ᴴ) ⟨i, p⟩ ⟨i, q⟩ =
        (1 : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ) ⟨i, p⟩ ⟨i, q⟩ := by
    intro i hM p q; rw [hM]
  have one_diag : ∀ (i : Fin 3) (p q : Fin n),
      (1 : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ) ⟨i, p⟩ ⟨i, q⟩ =
      (1 : Matrix (Fin n) (Fin n) ℂ) p q := by
    intro i p q
    by_cases hpq : p = q
    · simp [Matrix.one_apply, hpq]
    · simp [Matrix.one_apply, hpq]
  constructor
  · intro hM
    refine ⟨?_, ?_, ?_⟩
    · ext p q
      have h := extract 0 hM p q
      rw [blockCyclic_mul_conjTranspose_apply] at h
      simp only [show ((0 : Fin 3) : ℕ) = 0 from rfl, and_self, ite_true] at h
      rw [one_diag] at h; exact h
    · ext p q
      have h := extract 1 hM p q
      rw [blockCyclic_mul_conjTranspose_apply] at h
      simp only [show ((1 : Fin 3) : ℕ) = 1 from rfl,
                 show ((0 : Fin 3) : ℕ) = 0 from rfl,
                 (by decide : (1 : ℕ) ≠ 0),
                 and_false, false_and, ite_false,
                 and_self, ite_true] at h
      rw [one_diag] at h; exact h
    · ext p q
      have h := extract 2 hM p q
      rw [blockCyclic_mul_conjTranspose_apply] at h
      simp only [show ((2 : Fin 3) : ℕ) = 2 from rfl,
                 show ((0 : Fin 3) : ℕ) = 0 from rfl,
                 show ((1 : Fin 3) : ℕ) = 1 from rfl,
                 (by decide : (2 : ℕ) ≠ 0), (by decide : (2 : ℕ) ≠ 1),
                 and_false, false_and, ite_false,
                 and_self, ite_true] at h
      rw [one_diag] at h; exact h
  · rintro ⟨hX, hY, hZ⟩
    ext ⟨i, p⟩ ⟨j, q⟩
    rw [blockCyclic_mul_conjTranspose_apply]
    -- Convert RHS goal: 1 ⟨i,p⟩ ⟨j,q⟩ = (i = j ∧ p = q ? 1 : 0)
    have h1 : (1 : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ) ⟨i, p⟩ ⟨j, q⟩ =
              (if i = j then (1 : Matrix (Fin n) (Fin n) ℂ) p q else 0) := by
      by_cases hij : i = j
      · subst hij
        rw [Matrix.one_apply, if_pos rfl]
        by_cases hpq : p = q
        · subst hpq; simp [Matrix.one_apply]
        · simp [Matrix.one_apply, hpq]
      · simp [Matrix.one_apply, Prod.mk.injEq, hij]
    rw [h1]
    fin_cases i <;> fin_cases j <;>
      simp only [show ((0 : Fin 3) : ℕ) = 0 from rfl,
                 show ((1 : Fin 3) : ℕ) = 1 from rfl,
                 show ((2 : Fin 3) : ℕ) = 2 from rfl,
                 (show (⟨0, by norm_num⟩ : Fin 3) = ⟨0, by norm_num⟩ from rfl),
                 and_self, true_and, and_true, ite_true, ite_false,
                 (by decide : (0 : ℕ) ≠ 1), (by decide : (1 : ℕ) ≠ 0),
                 (by decide : (0 : ℕ) ≠ 2), (by decide : (2 : ℕ) ≠ 0),
                 (by decide : (1 : ℕ) ≠ 2), (by decide : (2 : ℕ) ≠ 1),
                 and_false, false_and, if_false, if_true,
                 (show ((0 : Fin 3) = (0 : Fin 3)) ↔ True from iff_of_true rfl trivial),
                 (show ((1 : Fin 3) = (1 : Fin 3)) ↔ True from iff_of_true rfl trivial),
                 (show ((2 : Fin 3) = (2 : Fin 3)) ↔ True from iff_of_true rfl trivial),
                 (show ((0 : Fin 3) = (1 : Fin 3)) ↔ False from
                    iff_of_false (by decide) (by exact False.elim)),
                 (show ((0 : Fin 3) = (2 : Fin 3)) ↔ False from
                    iff_of_false (by decide) (by exact False.elim)),
                 (show ((1 : Fin 3) = (0 : Fin 3)) ↔ False from
                    iff_of_false (by decide) (by exact False.elim)),
                 (show ((1 : Fin 3) = (2 : Fin 3)) ↔ False from
                    iff_of_false (by decide) (by exact False.elim)),
                 (show ((2 : Fin 3) = (0 : Fin 3)) ↔ False from
                    iff_of_false (by decide) (by exact False.elim)),
                 (show ((2 : Fin 3) = (1 : Fin 3)) ↔ False from
                    iff_of_false (by decide) (by exact False.elim))] <;>
      first
      | (have := congr_fun (congr_fun hX p) q; exact this)
      | (have := congr_fun (congr_fun hY p) q; exact this)
      | (have := congr_fun (congr_fun hZ p) q; exact this)
      | rfl

/-- `(blockCyclic X Y Z)³ = 1` iff `XYZ = 1` and `YZX = 1` and `ZXY = 1`.
    Note that any one of these implies the others by `XYZ = 1 ⇒ YZ = X⁻¹
    ⇒ YZX = X⁻¹ X = 1` and similarly for `ZXY`. -/
theorem blockCyclic_cb_eq_one_iff (X Y Z : Matrix (Fin n) (Fin n) ℂ) :
    blockCyclic X Y Z * blockCyclic X Y Z * blockCyclic X Y Z = 1 ↔
    X * Y * Z = 1 ∧ Y * Z * X = 1 ∧ Z * X * Y = 1 := by
  classical
  rw [Matrix.mul_assoc, blockCyclic_mul_self, blockCyclic_mul_blockCyclicSq]
  -- Goal now: blockCyclicCb X Y Z = 1 ↔ XYZ = 1 ∧ YZX = 1 ∧ ZXY = 1
  have one_diag : ∀ (i : Fin 3) (p q : Fin n),
      (1 : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ) ⟨i, p⟩ ⟨i, q⟩ =
      (1 : Matrix (Fin n) (Fin n) ℂ) p q := by
    intro i p q
    by_cases hpq : p = q
    · simp [Matrix.one_apply, hpq]
    · simp [Matrix.one_apply, hpq]
  constructor
  · intro hM
    refine ⟨?_, ?_, ?_⟩
    · ext p q
      have h := congr_fun (congr_fun hM ⟨0, p⟩) ⟨0, q⟩
      unfold blockCyclicCb at h
      simp only [show ((0 : Fin 3) : ℕ) = 0 from rfl, and_self, ite_true] at h
      rw [one_diag] at h; exact h
    · ext p q
      have h := congr_fun (congr_fun hM ⟨1, p⟩) ⟨1, q⟩
      unfold blockCyclicCb at h
      simp only [show ((1 : Fin 3) : ℕ) = 1 from rfl,
                 show ((0 : Fin 3) : ℕ) = 0 from rfl,
                 (by decide : (1 : ℕ) ≠ 0),
                 and_false, false_and, ite_false,
                 and_self, ite_true] at h
      rw [one_diag] at h; exact h
    · ext p q
      have h := congr_fun (congr_fun hM ⟨2, p⟩) ⟨2, q⟩
      unfold blockCyclicCb at h
      simp only [show ((2 : Fin 3) : ℕ) = 2 from rfl,
                 show ((0 : Fin 3) : ℕ) = 0 from rfl,
                 show ((1 : Fin 3) : ℕ) = 1 from rfl,
                 (by decide : (2 : ℕ) ≠ 0), (by decide : (2 : ℕ) ≠ 1),
                 and_false, false_and, ite_false,
                 and_self, ite_true] at h
      rw [one_diag] at h; exact h
  · rintro ⟨hXYZ, hYZX, hZXY⟩
    ext ⟨i, p⟩ ⟨j, q⟩
    unfold blockCyclicCb
    have h1 : (1 : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ) ⟨i, p⟩ ⟨j, q⟩ =
              (if i = j then (1 : Matrix (Fin n) (Fin n) ℂ) p q else 0) := by
      by_cases hij : i = j
      · subst hij
        rw [Matrix.one_apply, if_pos rfl]
        by_cases hpq : p = q
        · subst hpq; simp [Matrix.one_apply]
        · simp [Matrix.one_apply, hpq]
      · simp [Matrix.one_apply, Prod.mk.injEq, hij]
    rw [h1]
    fin_cases i <;> fin_cases j <;>
      simp only [show ((0 : Fin 3) : ℕ) = 0 from rfl,
                 show ((1 : Fin 3) : ℕ) = 1 from rfl,
                 show ((2 : Fin 3) : ℕ) = 2 from rfl,
                 and_self, true_and, and_true, ite_true, ite_false,
                 (by decide : (0 : ℕ) ≠ 1), (by decide : (1 : ℕ) ≠ 0),
                 (by decide : (0 : ℕ) ≠ 2), (by decide : (2 : ℕ) ≠ 0),
                 (by decide : (1 : ℕ) ≠ 2), (by decide : (2 : ℕ) ≠ 1),
                 and_false, false_and, if_false, if_true,
                 (show ((0 : Fin 3) = (1 : Fin 3)) ↔ False from
                    iff_of_false (by decide) (by exact False.elim)),
                 (show ((0 : Fin 3) = (2 : Fin 3)) ↔ False from
                    iff_of_false (by decide) (by exact False.elim)),
                 (show ((1 : Fin 3) = (0 : Fin 3)) ↔ False from
                    iff_of_false (by decide) (by exact False.elim)),
                 (show ((1 : Fin 3) = (2 : Fin 3)) ↔ False from
                    iff_of_false (by decide) (by exact False.elim)),
                 (show ((2 : Fin 3) = (0 : Fin 3)) ↔ False from
                    iff_of_false (by decide) (by exact False.elim)),
                 (show ((2 : Fin 3) = (1 : Fin 3)) ↔ False from
                    iff_of_false (by decide) (by exact False.elim))] <;>
      first
      | (have := congr_fun (congr_fun hXYZ p) q; exact this)
      | (have := congr_fun (congr_fun hYZX p) q; exact this)
      | (have := congr_fun (congr_fun hZXY p) q; exact this)
      | rfl

/-! ## Reindex to `Fin (3*n)` so the Schur axiom applies

The Schur axiom `matrix_unitary_schur_form` is stated for
`Matrix (Fin N) (Fin N) ℂ` with the natural `Fin N` linear order. The
block-cyclic matrix as defined above is indexed by `Fin 3 × Fin n`
(no built-in linear order). We reindex to `Fin (3 * n)` via the
canonical bijection `finProdFinEquiv` so the axiom applies. -/

/-- The block-cyclic matrix re-indexed to `Fin (3 * n)`. -/
noncomputable def blockCyclicFin (X Y Z : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin (3 * n)) (Fin (3 * n)) ℂ :=
  (blockCyclic X Y Z).submatrix finProdFinEquiv.symm finProdFinEquiv.symm

/-- The Schur axiom applied to the reindexed block-cyclic matrix:
    there exists a unitary `U` putting `blockCyclicFin X Y Z` in upper
    triangular form. -/
theorem blockCyclicFin_schur_form (X Y Z : Matrix (Fin n) (Fin n) ℂ) :
    ∃ U : Matrix (Fin (3 * n)) (Fin (3 * n)) ℂ,
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      IsUpperTriangular (Uᴴ * blockCyclicFin X Y Z * U) :=
  matrix_unitary_schur_form (blockCyclicFin X Y Z)

/-- `Tr(M·M·M) = 3 · Tr(X·Y·Z)` for the block-cyclic `M`. -/
theorem trace_blockCyclic_cb (X Y Z : Matrix (Fin n) (Fin n) ℂ) :
    (blockCyclic X Y Z * blockCyclic X Y Z * blockCyclic X Y Z).trace =
    3 * (X * Y * Z).trace := by
  rw [Matrix.mul_assoc, blockCyclic_mul_self, blockCyclic_mul_blockCyclicSq]
  -- Tr(blockCyclicCb) = Σ_{ip} blockCyclicCb(ip)(ip)
  show (∑ ip : Fin 3 × Fin n, blockCyclicCb X Y Z ip ip) = _
  rw [Fintype.sum_prod_type, Fin.sum_univ_three]
  simp only [blockCyclicCb,
             show ((0 : Fin 3) : ℕ) = 0 from rfl,
             show ((1 : Fin 3) : ℕ) = 1 from rfl,
             show ((2 : Fin 3) : ℕ) = 2 from rfl,
             and_self, ite_true,
             Nat.zero_ne_one, Nat.one_ne_zero,
             (by decide : (0 : ℕ) ≠ 2), (by decide : (2 : ℕ) ≠ 0),
             (by decide : (1 : ℕ) ≠ 2), (by decide : (2 : ℕ) ≠ 1),
             and_false, false_and, if_false, ite_false]
  -- After simp: Σ_p (XYZ p p) + Σ_p (YZX p p) + Σ_p (ZXY p p)
  -- which is (XYZ).trace + (YZX).trace + (ZXY).trace
  rw [show (∑ p : Fin n, (X * Y * Z) p p) = (X * Y * Z).trace from rfl]
  rw [show (∑ p : Fin n, (Y * Z * X) p p) = (Y * Z * X).trace from rfl]
  rw [show (∑ p : Fin n, (Z * X * Y) p p) = (Z * X * Y).trace from rfl]
  -- Trace cyclicity: Tr(YZX) = Tr(XYZ), Tr(ZXY) = Tr(XYZ).
  rw [show (Y * Z * X).trace = (X * Y * Z).trace from by
        rw [Matrix.trace_mul_comm (Y * Z) X, ← mul_assoc]]
  rw [show (Z * X * Y).trace = (X * Y * Z).trace from by
        rw [mul_assoc Z X Y, Matrix.trace_mul_comm Z (X * Y)]]
  ring

/-- Squaring commutes with the reindex: `(M.submatrix e e)² = (M²).submatrix e e`. -/
theorem blockCyclicFin_mul_self (X Y Z : Matrix (Fin n) (Fin n) ℂ) :
    blockCyclicFin X Y Z * blockCyclicFin X Y Z =
    (blockCyclic X Y Z * blockCyclic X Y Z).submatrix
      finProdFinEquiv.symm finProdFinEquiv.symm := by
  unfold blockCyclicFin
  rw [Matrix.submatrix_mul_equiv]

/-- Cubing commutes with the reindex. -/
theorem blockCyclicFin_mul_self_mul_self (X Y Z : Matrix (Fin n) (Fin n) ℂ) :
    blockCyclicFin X Y Z * blockCyclicFin X Y Z * blockCyclicFin X Y Z =
    (blockCyclic X Y Z * blockCyclic X Y Z * blockCyclic X Y Z).submatrix
      finProdFinEquiv.symm finProdFinEquiv.symm := by
  rw [blockCyclicFin_mul_self]
  unfold blockCyclicFin
  rw [Matrix.submatrix_mul_equiv]

/-- The Frobenius² of `M_fin · M_fin` decomposes cyclically:
    `‖M_fin·M_fin‖²_F = ‖XY‖² + ‖YZ‖² + ‖ZX‖²`. -/
theorem frobNormSq_F_blockCyclicFin_sq (X Y Z : Matrix (Fin n) (Fin n) ℂ) :
    frobNormSq_F (blockCyclicFin X Y Z * blockCyclicFin X Y Z) =
    frobNormSq_F (X * Y) + frobNormSq_F (Y * Z) + frobNormSq_F (Z * X) := by
  rw [blockCyclicFin_mul_self, frobNormSq_F_submatrix_equiv,
      frobNormSq_F_blockCyclic_sq]

/-- `Tr(M_fin · M_fin · M_fin) = 3 · Tr(X·Y·Z)` for the reindexed block-cyclic. -/
theorem trace_blockCyclicFin_cb (X Y Z : Matrix (Fin n) (Fin n) ℂ) :
    (blockCyclicFin X Y Z * blockCyclicFin X Y Z * blockCyclicFin X Y Z).trace =
    3 * (X * Y * Z).trace := by
  rw [blockCyclicFin_mul_self_mul_self, trace_submatrix_equiv, trace_blockCyclic_cb]

/-! ## Schur trace bound on the reindexed block-cyclic matrix

Combining Schur's triangulation with the upper-triangular trace bound
`‖Tr(T³)‖⁴ ≤ N · (‖T²‖²_F)³` and the unitary invariance of trace and
Frobenius² yields the central inequality:
  `‖Tr(M_fin³)‖⁴ ≤ (3n) · (‖M_fin²‖²_F)³`
which translates via the entry-wise identities to
  `81 · ‖Tr(XYZ)‖⁴ ≤ (3n) · (‖XY‖²_F + ‖YZ‖²_F + ‖ZX‖²_F)³`. -/

/-- Schur trace bound on the block-cyclic matrix, in raw form:
    `‖Tr(M_fin³)‖⁴ ≤ (3n) · (‖M_fin²‖²_F)³`. -/
theorem matrix_schur_trace_bound_blockCyclicFin
    (X Y Z : Matrix (Fin n) (Fin n) ℂ) :
    ‖(blockCyclicFin X Y Z * blockCyclicFin X Y Z * blockCyclicFin X Y Z).trace‖ ^ 4 ≤
    (3 * n : ℝ) *
      frobNormSq_F (blockCyclicFin X Y Z * blockCyclicFin X Y Z) ^ 3 := by
  obtain ⟨U, hUU, hUU', hUTri⟩ :=
    matrix_unitary_schur_form (blockCyclicFin X Y Z)
  have hcard : (Fintype.card (Fin (3 * n)) : ℝ) = (3 * n : ℝ) := by
    simp [Fintype.card_fin]
  have htrace_eq :
      (blockCyclicFin X Y Z * blockCyclicFin X Y Z * blockCyclicFin X Y Z).trace =
      ((Uᴴ * blockCyclicFin X Y Z * U) *
       (Uᴴ * blockCyclicFin X Y Z * U) *
       (Uᴴ * blockCyclicFin X Y Z * U)).trace :=
    (trace_unitary_conj_cb hUU').symm
  have hfrob_eq :
      frobNormSq_F (blockCyclicFin X Y Z * blockCyclicFin X Y Z) =
      frobNormSq_F (Uᴴ * blockCyclicFin X Y Z * U *
                    (Uᴴ * blockCyclicFin X Y Z * U)) :=
    (frobNormSq_F_unitary_conj_sq hUU hUU').symm
  rw [htrace_eq, hfrob_eq, ← hcard]
  exact hUTri.norm_trace_cubed_pow_four_le

/-- Schur trace bound on `(X, Y, Z)`:
    `‖3·Tr(XYZ)‖⁴ ≤ (3n) · (‖XY‖²_F + ‖YZ‖²_F + ‖ZX‖²_F)³`. -/
theorem matrix_schur_trace_bound_xyz (X Y Z : Matrix (Fin n) (Fin n) ℂ) :
    ‖3 * (X * Y * Z).trace‖ ^ 4 ≤
    (3 * n : ℝ) *
      (frobNormSq_F (X * Y) + frobNormSq_F (Y * Z) + frobNormSq_F (Z * X)) ^ 3 := by
  rw [← trace_blockCyclicFin_cb, ← frobNormSq_F_blockCyclicFin_sq]
  exact matrix_schur_trace_bound_blockCyclicFin X Y Z

/-! ## Reindex versions of the unitarity correspondences -/

/-- Submatrix by an equiv is injective on matrix equality. -/
theorem submatrix_inj_of_equiv {α m l : Type*} (e : l ≃ m)
    (M N : Matrix m m α) :
    M.submatrix e e = N.submatrix e e ↔ M = N := by
  constructor
  · intro h
    ext p q
    have hpq := congr_fun (congr_fun h (e.symm p)) (e.symm q)
    simp only [Matrix.submatrix_apply, Equiv.apply_symm_apply] at hpq
    exact hpq
  · intro h; rw [h]

/-- `blockCyclicFin X Y Z` is unitary iff each of `X, Y, Z` is unitary. -/
theorem blockCyclicFin_mul_conjTranspose_eq_one_iff
    (X Y Z : Matrix (Fin n) (Fin n) ℂ) :
    blockCyclicFin X Y Z * (blockCyclicFin X Y Z)ᴴ = 1 ↔
    X * Xᴴ = 1 ∧ Y * Yᴴ = 1 ∧ Z * Zᴴ = 1 := by
  unfold blockCyclicFin
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  rw [show (1 : Matrix (Fin (3 * n)) (Fin (3 * n)) ℂ) =
          (1 : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ).submatrix
            finProdFinEquiv.symm finProdFinEquiv.symm from
        (Matrix.submatrix_one_equiv finProdFinEquiv.symm).symm]
  rw [submatrix_inj_of_equiv]
  exact blockCyclic_mul_conjTranspose_eq_one_iff X Y Z

/-- `(blockCyclicFin X Y Z)³ = 1` iff `XYZ = YZX = ZXY = 1`. -/
theorem blockCyclicFin_cb_eq_one_iff
    (X Y Z : Matrix (Fin n) (Fin n) ℂ) :
    blockCyclicFin X Y Z * blockCyclicFin X Y Z * blockCyclicFin X Y Z = 1 ↔
    X * Y * Z = 1 ∧ Y * Z * X = 1 ∧ Z * X * Y = 1 := by
  rw [blockCyclicFin_mul_self_mul_self]
  rw [show (1 : Matrix (Fin (3 * n)) (Fin (3 * n)) ℂ) =
          (1 : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ).submatrix
            finProdFinEquiv.symm finProdFinEquiv.symm from
        (Matrix.submatrix_one_equiv finProdFinEquiv.symm).symm]
  rw [submatrix_inj_of_equiv]
  exact blockCyclic_cb_eq_one_iff X Y Z

end
