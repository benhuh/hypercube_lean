/-
  HyperCubeGroup.Plancherel

  Structural Plancherel / Parseval infrastructure for the HyperCube model.
  Everything in this file is unconditionally proved.

  Contents:

    1. `H_eq_mass_matrix_form` — for any quasigroup `f`,
       `ℋ(Θ) = (1/n) [Tr(R_A · L_B) + Tr(R_B · L_C) + Tr(R_C · L_A)]`,
       where `R_X := Σ_x X_x† X_x`, `L_X := Σ_x X_x X_x†`. Pure
       algebra; no abelian assumption.

    2. `CharacterBasis` — a structure packaging an orthonormal complete
       character system (Pontryagin duality for finite abelian groups)
       as a hypothesis, so this file is independent of how the basis
       is sourced.

    3. `mFourier`, `mFourier'` — matrix-valued Fourier transforms with
       conjugate / non-conjugate kernels.

    4. `mass_R_eq_fourier_sum`, `mass_L_eq_fourier_sum` — Plancherel
       identities for the mass matrices:
         `Σ_a A_a† A_a = (1/n) Σ_χ Â_χ† Â_χ`,
         `Σ_a A_a A_a† = (1/n) Σ_χ Â_χ Â_χ†`.
-/

import HyperCubeGroup.Decomposition

open Matrix BigOperators Finset Complex

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ## 0. Character (single source of truth) -/

/-- A character of a finite (abelian) group: a unit-modulus
    homomorphism to `ℂ`. -/
structure Character (f : BinOp n) where
  val : Fin n → ℂ
  hom : ∀ a b : Fin n, val (f.op a b) = val a * val b
  unit : ∀ a : Fin n, Complex.normSq (val a) = 1

/-! ## 1. Mass matrices and the rewrite of H -/

/-- Right Gram mass matrix `R_X := Σ_x X_x† · X_x` (PSD). -/
def massR (X : Fin n → Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ x : Fin n, (X x).conjTranspose * X x

/-- Left Gram mass matrix `L_X := Σ_x X_x · X_x†` (PSD). -/
def massL (X : Fin n → Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ x : Fin n, X x * (X x).conjTranspose

/-- For a single pair `(X, Y)`,
      `‖X · Y‖² = (1/n) · Tr((X† X) · (Y Y†))`. -/
private theorem frobNormSq_mul_eq_trace
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    frobNormSq (X * Y) =
      (1 / (n : ℂ)) * (X.conjTranspose * X * (Y * Y.conjTranspose)).trace := by
  show frobInner (X * Y) (X * Y) = _
  unfold frobInner
  congr 1
  -- Goal: Tr((XY)† · (XY)) = Tr((X†X) · (YY†))
  -- Via cyclicity: Tr(Y† X† X Y) = Tr(X† X Y Y†)
  rw [Matrix.conjTranspose_mul]
  calc (Y.conjTranspose * X.conjTranspose * (X * Y)).trace
      = (Y.conjTranspose * (X.conjTranspose * (X * Y))).trace := by
        rw [Matrix.mul_assoc]
    _ = ((X.conjTranspose * (X * Y)) * Y.conjTranspose).trace := by
        rw [Matrix.trace_mul_comm]
    _ = (X.conjTranspose * X * Y * Y.conjTranspose).trace := by
        rw [Matrix.mul_assoc X.conjTranspose X Y]
    _ = (X.conjTranspose * X * (Y * Y.conjTranspose)).trace := by
        rw [Matrix.mul_assoc (X.conjTranspose * X) Y Y.conjTranspose]

/-- Sum of pair-Frobenius² collapses to a trace of mass matrices:
      `Σ_{x,y} ‖X_x · Y_y‖² = (1/n) · Tr(R_X · L_Y)`. -/
private theorem sum_pair_frobNormSq_eq_trace
    (X Y : Fin n → Matrix (Fin n) (Fin n) ℂ) :
    ∑ x : Fin n, ∑ y : Fin n, frobNormSq (X x * Y y) =
      (1 / (n : ℂ)) * (massR X * massL Y).trace := by
  simp_rw [frobNormSq_mul_eq_trace]
  -- pull (1/n) outside both sums
  simp_rw [← Finset.mul_sum]
  congr 1
  -- Σ_x Σ_y Tr(X†_x X_x · Y_y Y†_y) = Tr(R_X · L_Y)
  show ∑ x : Fin n, ∑ y : Fin n,
        ((X x).conjTranspose * X x * (Y y * (Y y).conjTranspose)).trace =
      (massR X * massL Y).trace
  -- Inner: pull the (X x)†(X x) out of the y-sum and collapse
  have hY : ∀ x : Fin n,
      ∑ y : Fin n,
        ((X x).conjTranspose * X x * (Y y * (Y y).conjTranspose)).trace =
      ((X x).conjTranspose * X x * massL Y).trace := by
    intro x
    show _ = ((X x).conjTranspose * X x *
              ∑ y : Fin n, Y y * (Y y).conjTranspose).trace
    rw [Matrix.mul_sum, Matrix.trace_sum]
  simp_rw [hY]
  -- Outer: collapse the x-sum
  show (∑ x : Fin n, ((X x).conjTranspose * X x * massL Y).trace) =
       (massR X * massL Y).trace
  rw [show massR X * massL Y =
        (∑ x : Fin n, (X x).conjTranspose * X x) * massL Y from rfl,
      Finset.sum_mul, Matrix.trace_sum]

/-- For a quasigroup `f`,
    `Σ_{a,b} ‖B_b · C_{a∘b}‖² = Σ_{b,c} ‖B_b · C_c‖²`. -/
private theorem sum_BC_support_eq_uniform (Θ : HCParams n) (f : BinOp n)
    (hq : IsQuasigroup f) :
    ∑ a : Fin n, ∑ b : Fin n, frobNormSq (Θ.B b * Θ.C (f.op a b)) =
      ∑ b : Fin n, ∑ c : Fin n, frobNormSq (Θ.B b * Θ.C c) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  let e : Fin n ≃ Fin n :=
    Equiv.ofBijective (fun a => f.op a b) (hq.right_cancel b)
  exact e.sum_comp (fun c => frobNormSq (Θ.B b * Θ.C c))

private theorem sum_CA_support_eq_uniform (Θ : HCParams n) (f : BinOp n)
    (hq : IsQuasigroup f) :
    ∑ a : Fin n, ∑ b : Fin n, frobNormSq (Θ.C (f.op a b) * Θ.A a) =
      ∑ c : Fin n, ∑ a : Fin n, frobNormSq (Θ.C c * Θ.A a) := by
  rw [show ∑ a : Fin n, ∑ b : Fin n, frobNormSq (Θ.C (f.op a b) * Θ.A a) =
        ∑ a : Fin n, ∑ c : Fin n, frobNormSq (Θ.C c * Θ.A a) from ?_]
  · exact Finset.sum_comm
  · apply Finset.sum_congr rfl
    intro a _
    let e : Fin n ≃ Fin n := Equiv.ofBijective (f.op a) (hq.left_cancel a)
    exact e.sum_comp (fun c => frobNormSq (Θ.C c * Θ.A a))

/-- **Mass-matrix rewrite of the objective.** For any quasigroup `f`,
      `ℋ(Θ) = (1/n) · [Tr(R_A L_B) + Tr(R_B L_C) + Tr(R_C L_A)]`.
    No abelian assumption is used. -/
theorem H_eq_mass_matrix_form (Θ : HCParams n) (f : BinOp n)
    (hq : IsQuasigroup f) :
    objective Θ f = (1 / (n : ℂ)) *
      ((massR Θ.A * massL Θ.B).trace +
       (massR Θ.B * massL Θ.C).trace +
       (massR Θ.C * massL Θ.A).trace) := by
  rw [objective_eq_sum_support]
  -- Split each ∑_b (X + Y + Z) into ∑_b X + ∑_b Y + ∑_b Z, then ∑_a similarly.
  simp_rw [Finset.sum_add_distrib]
  -- Now goal LHS is a sum of 3 double-sums (each the cyclic Frobenius²).
  -- Convert the BC and CA pieces from "support indexed by (a,b)" to (b,c) / (a,c).
  rw [sum_BC_support_eq_uniform Θ f hq, sum_CA_support_eq_uniform Θ f hq]
  -- Apply the trace identity to each pair-sum.
  rw [sum_pair_frobNormSq_eq_trace Θ.B Θ.C,
      sum_pair_frobNormSq_eq_trace Θ.C Θ.A,
      sum_pair_frobNormSq_eq_trace Θ.A Θ.B]
  ring

/-! ## 2. Character basis and matrix-valued Fourier transform -/

/-- Orthonormal complete character basis (Pontryagin dual of an abelian
    group). Stated as a structure of hypotheses so this file is
    independent of how the basis is sourced. -/
structure CharacterBasis (f : BinOp n) where
  chars : Fin n → Character f
  /-- Orthogonality: `(1/n) Σ_g χ_i(g) · conj(χ_j(g)) = 𝟙{i=j}`. -/
  orth : ∀ i j : Fin n,
    (1 / (n : ℂ)) * ∑ g : Fin n, (chars i).val g * starRingEnd ℂ ((chars j).val g) =
      if i = j then 1 else 0
  /-- Completeness: `(1/n) Σ_χ χ(g) · conj(χ(h)) = 𝟙{g=h}`. -/
  comp : ∀ g h : Fin n,
    (1 / (n : ℂ)) * ∑ i : Fin n, (chars i).val g * starRingEnd ℂ ((chars i).val h) =
      if g = h then 1 else 0

namespace CharacterBasis

variable {f : BinOp n}

/-- Helper: cancel the `1/n` factor in completeness:
    `Σ_i χ_i(g) χ̄_i(h) = n · 𝟙{g=h}`. -/
theorem comp_unscaled (cb : CharacterBasis f) (g h : Fin n) :
    ∑ i : Fin n, (cb.chars i).val g * starRingEnd ℂ ((cb.chars i).val h) =
      if g = h then (n : ℂ) else 0 := by
  have hnz : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  calc ∑ i : Fin n, (cb.chars i).val g * starRingEnd ℂ ((cb.chars i).val h)
      = (n : ℂ) * ((1 / (n : ℂ)) *
          ∑ i : Fin n, (cb.chars i).val g * starRingEnd ℂ ((cb.chars i).val h)) := by
        field_simp
    _ = (n : ℂ) * (if g = h then (1 : ℂ) else 0) := by rw [cb.comp g h]
    _ = if g = h then (n : ℂ) else 0 := by split_ifs <;> simp

/-- Sum-swap version of completeness: `Σ_i χ̄_i(g) χ_i(h) = n · 𝟙{g=h}`. -/
theorem comp_unscaled' (cb : CharacterBasis f) (g h : Fin n) :
    ∑ i : Fin n, starRingEnd ℂ ((cb.chars i).val g) * (cb.chars i).val h =
      if g = h then (n : ℂ) else 0 := by
  rw [show (∑ i : Fin n, starRingEnd ℂ ((cb.chars i).val g) * (cb.chars i).val h)
      = (∑ i : Fin n, (cb.chars i).val h * starRingEnd ℂ ((cb.chars i).val g))
      from by apply Finset.sum_congr rfl; intros; ring]
  rw [cb.comp_unscaled h g]
  by_cases hgh : g = h
  · subst hgh; simp
  · rw [if_neg hgh, if_neg (fun heq => hgh heq.symm)]

/-- Unscaled orthogonality: `Σ_g χ_i(g) χ̄_j(g) = n · 𝟙{i=j}`. -/
theorem orth_unscaled (cb : CharacterBasis f) (i j : Fin n) :
    ∑ g : Fin n, (cb.chars i).val g * starRingEnd ℂ ((cb.chars j).val g) =
      if i = j then (n : ℂ) else 0 := by
  have hnz : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  calc ∑ g : Fin n, (cb.chars i).val g * starRingEnd ℂ ((cb.chars j).val g)
      = (n : ℂ) * ((1 / (n : ℂ)) *
          ∑ g : Fin n, (cb.chars i).val g * starRingEnd ℂ ((cb.chars j).val g)) := by
        field_simp
    _ = (n : ℂ) * (if i = j then (1 : ℂ) else 0) := by rw [cb.orth i j]
    _ = if i = j then (n : ℂ) else 0 := by split_ifs <;> simp

/-- Sum-swap version of orthogonality: `Σ_g χ̄_i(g) χ_k(g) = n · 𝟙{i=k}`. -/
theorem orth_unscaled' (cb : CharacterBasis f) (i k : Fin n) :
    ∑ g : Fin n, starRingEnd ℂ ((cb.chars i).val g) * (cb.chars k).val g =
      if i = k then (n : ℂ) else 0 := by
  rw [show (∑ g : Fin n, starRingEnd ℂ ((cb.chars i).val g) * (cb.chars k).val g)
        = (∑ g : Fin n, (cb.chars k).val g * starRingEnd ℂ ((cb.chars i).val g)) from
      by apply Finset.sum_congr rfl; intros; ring]
  rw [cb.orth_unscaled k i]
  by_cases hik : i = k
  · subst hik; simp
  · rw [if_neg hik, if_neg (fun heq => hik heq.symm)]

/-- Matrix-valued Fourier transform with conjugate kernel:
      `Â_χ := Σ_a conj(χ(a)) · A_a`. -/
def mFourier (cb : CharacterBasis f) (X : Fin n → Matrix (Fin n) (Fin n) ℂ)
    (i : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ a : Fin n, (starRingEnd ℂ ((cb.chars i).val a)) • X a

/-- Variant Fourier transform for the `C`-slot:
      `Č_χ := Σ_c χ(c) · C_c`. -/
def mFourier' (cb : CharacterBasis f) (X : Fin n → Matrix (Fin n) (Fin n) ℂ)
    (i : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ a : Fin n, (cb.chars i).val a • X a

/-! ## 3. Plancherel for mass matrices -/

/-- **Plancherel for the right Gram mass matrix.**
    `Σ_a A_a† · A_a = (1/n) · Σ_χ Â_χ† · Â_χ`. -/
theorem mass_R_eq_fourier_sum (cb : CharacterBasis f)
    (X : Fin n → Matrix (Fin n) (Fin n) ℂ) :
    massR X = (1 / (n : ℂ)) •
      ∑ i : Fin n, (cb.mFourier X i).conjTranspose * cb.mFourier X i := by
  -- Strategy: expand each (Â_i)† Â_i, swap sums, apply unscaled completeness.
  have hexpand : ∀ i : Fin n,
      (cb.mFourier X i).conjTranspose * cb.mFourier X i =
      ∑ a : Fin n, ∑ a' : Fin n,
        ((cb.chars i).val a * starRingEnd ℂ ((cb.chars i).val a')) •
          ((X a).conjTranspose * X a') := by
    intro i
    -- (Σ_a (χ̄ a • X_a))† * (Σ_a' (χ̄ a' • X_a'))
    -- = (Σ_a (χ̄ a)† • (X_a)†) * (Σ_a' (χ̄ a' • X_a'))
    -- = Σ_a Σ_a' ((χ̄ a)† * (χ̄ a')) • ((X_a)† * X_a')
    show (∑ a : Fin n, (starRingEnd ℂ ((cb.chars i).val a)) • X a).conjTranspose *
          (∑ a' : Fin n, (starRingEnd ℂ ((cb.chars i).val a')) • X a') = _
    rw [Matrix.conjTranspose_sum]
    -- Now: (Σ_a ((χ̄ a) • X_a)†) * (Σ_a' (χ̄ a' • X_a'))
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Matrix.conjTranspose_smul, Matrix.mul_sum]
    apply Finset.sum_congr rfl
    intro a' _
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    -- star (starRingEnd ℂ z) = z
    show star (starRingEnd ℂ ((cb.chars i).val a)) *
          starRingEnd ℂ ((cb.chars i).val a') =
        (cb.chars i).val a * starRingEnd ℂ ((cb.chars i).val a')
    rw [show star (starRingEnd ℂ ((cb.chars i).val a)) = (cb.chars i).val a from by
        rw [starRingEnd_apply, star_star]]
  simp_rw [hexpand]
  -- Swap (i, a, a') → (a, a', i), then apply completeness
  rw [show (∑ i : Fin n, ∑ a : Fin n, ∑ a' : Fin n,
            ((cb.chars i).val a * starRingEnd ℂ ((cb.chars i).val a')) •
              ((X a).conjTranspose * X a'))
        = (∑ a : Fin n, ∑ a' : Fin n,
            (∑ i : Fin n,
              (cb.chars i).val a * starRingEnd ℂ ((cb.chars i).val a')) •
                ((X a).conjTranspose * X a')) from ?_]
  · -- Apply unscaled completeness Σ_i χ_i(a) χ̄_i(a') = n · 𝟙{a=a'}
    simp_rw [cb.comp_unscaled]
    -- Now: (1/n) • Σ_a Σ_a' (𝟙{a=a'} · n) • ((X_a)† X_a')
    --    = (1/n) • Σ_a (n • ((X_a)† X_a)) = Σ_a (X_a)† X_a = R_A
    rw [show (∑ a : Fin n, ∑ a' : Fin n,
              (if a = a' then (n : ℂ) else 0) • ((X a).conjTranspose * X a'))
          = ∑ a : Fin n, (n : ℂ) • ((X a).conjTranspose * X a) from ?_]
    · rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [smul_smul, one_div,
          inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne n)), one_smul]
    · apply Finset.sum_congr rfl
      intro a _
      -- Σ_a' (𝟙{a=a'} · n) • ((X a)† X a') = n • ((X a)† X a)
      rw [show (∑ a' : Fin n,
                (if a = a' then (n : ℂ) else 0) • ((X a).conjTranspose * X a'))
            = (n : ℂ) • ((X a).conjTranspose * X a) from ?_]
      apply Eq.symm
      rw [show ((n : ℂ) • ((X a).conjTranspose * X a))
            = (∑ a' : Fin n, if a = a' then ((n : ℂ) • ((X a).conjTranspose * X a'))
                              else 0) from ?_]
      · apply Finset.sum_congr rfl
        intro a' _
        split_ifs with h
        · subst h; rfl
        · rw [zero_smul]
      · rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  · -- Sum-swap (i, a, a') → (a, a', i)
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a' _
    rw [← Finset.sum_smul]

/-- **Plancherel for the left Gram mass matrix.**
    `Σ_a A_a · A_a† = (1/n) · Σ_χ Â_χ · Â_χ†`. -/
theorem mass_L_eq_fourier_sum (cb : CharacterBasis f)
    (X : Fin n → Matrix (Fin n) (Fin n) ℂ) :
    massL X = (1 / (n : ℂ)) •
      ∑ i : Fin n, cb.mFourier X i * (cb.mFourier X i).conjTranspose := by
  -- Strategy: same shape as mass_R, with X · X† instead.
  have hexpand : ∀ i : Fin n,
      cb.mFourier X i * (cb.mFourier X i).conjTranspose =
      ∑ a : Fin n, ∑ a' : Fin n,
        (starRingEnd ℂ ((cb.chars i).val a) * (cb.chars i).val a') •
          (X a * (X a').conjTranspose) := by
    intro i
    show (∑ a : Fin n, (starRingEnd ℂ ((cb.chars i).val a)) • X a) *
          (∑ a' : Fin n, (starRingEnd ℂ ((cb.chars i).val a')) • X a').conjTranspose =
        _
    rw [Matrix.conjTranspose_sum]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Matrix.mul_sum]
    apply Finset.sum_congr rfl
    intro a' _
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    -- χ̄(a) * star(χ̄(a')) = χ̄(a) * χ(a')
    show (starRingEnd ℂ ((cb.chars i).val a)) *
          star (starRingEnd ℂ ((cb.chars i).val a')) =
        starRingEnd ℂ ((cb.chars i).val a) * (cb.chars i).val a'
    rw [show star (starRingEnd ℂ ((cb.chars i).val a')) = (cb.chars i).val a' from by
        rw [starRingEnd_apply, star_star]]
  simp_rw [hexpand]
  rw [show (∑ i : Fin n, ∑ a : Fin n, ∑ a' : Fin n,
            (starRingEnd ℂ ((cb.chars i).val a) * (cb.chars i).val a') •
              (X a * (X a').conjTranspose))
        = (∑ a : Fin n, ∑ a' : Fin n,
            (∑ i : Fin n,
              starRingEnd ℂ ((cb.chars i).val a) * (cb.chars i).val a') •
                (X a * (X a').conjTranspose)) from ?_]
  · simp_rw [cb.comp_unscaled']
    rw [show (∑ a : Fin n, ∑ a' : Fin n,
              (if a = a' then (n : ℂ) else 0) • (X a * (X a').conjTranspose))
          = ∑ a : Fin n, (n : ℂ) • (X a * (X a).conjTranspose) from ?_]
    · rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [smul_smul, one_div,
          inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne n)), one_smul]
    · apply Finset.sum_congr rfl
      intro a _
      rw [show ((n : ℂ) • (X a * (X a).conjTranspose))
            = (∑ a' : Fin n, if a = a' then ((n : ℂ) • (X a * (X a').conjTranspose))
                              else 0) from ?_]
      · apply Eq.symm
        apply Finset.sum_congr rfl
        intro a' _
        split_ifs with h
        · subst h; rfl
        · rw [zero_smul]
      · rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a' _
    rw [← Finset.sum_smul]

end CharacterBasis

end
