/-
  HyperCubeGroup.Decomposition

  The orthogonal decomposition ℋ = ℬ + ℛ (Section 3).

  Main results:
  - Definition 4 (Inverse-Scale Penalty): ℬ_δ(Θ) = Σ δ_abc |T_abc|² (1/‖A_a‖² + 1/‖B_b‖² + 1/‖C_c‖²)
  - Definition 4 (Misalignment Penalty): ℛ_δ(Θ) = Σ δ_abc (‖Δ^(A)_abc‖² + ‖Δ^(B)_abc‖² + ‖Δ^(C)_abc‖²)
    where Δ^(A)_abc = (B_b C_c)† - T*_abc A_a / ‖A_a‖²
  - Lemma 1 (Decomposition of ℋ): ℋ(Θ) = ℬ_δ(Θ) + ℛ_δ(Θ) with ℛ_δ(Θ) ≥ 0,
    and ℛ_δ(Θ) = 0 iff perfect collinearity holds.
-/

import HyperCubeGroup.Basic
open Matrix BigOperators Finset

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ## Cauchy-Schwarz bound on the Jacobian -/

-- Helper lemmas are defined below; frobInner_cauchy_schwarz and
-- cauchySchwarz_jacobian follow after star_frobNormSq et al.

-- cauchySchwarz_jacobian and jacobian_lower_bound are proved below
-- after the helper lemmas.

/-! ## Definition 4 (inverse-scale half): Inverse-Scale Penalty B -/

/-- The inverse-scale penalty ℬ_δ(Θ) (Definition 4, Eq. 5):
    B = Σ δ_abc |T_abc|² (1/‖A_a‖² + 1/‖B_b‖² + 1/‖C_c‖²). -/
def inverseScalePenalty (Θ : HCParams n) (f : BinOp n) : ℂ :=
  ∑ a : Fin n, ∑ b : Fin n,
    let c := f.op a b
    let t := hcProduct Θ a b c
    t * starRingEnd ℂ t *
      (1 / frobNormSq (Θ.A a) +
       1 / frobNormSq (Θ.B b) +
       1 / frobNormSq (Θ.C c))

/-! ## Definition 4 (misalignment half): Misalignment Penalty R -/

/-- The misalignment residual Δ^(A)_abc: the component of (B_b C_c)†
    orthogonal to A_a.
    Δ^(A)_abc = (B_b C_c)† - (T*_abc / ‖A_a‖²) A_a -/
def misalignmentResidualA (Θ : HCParams n) (a b c : Fin n) :
    Matrix (Fin n) (Fin n) ℂ :=
  (Θ.B b * Θ.C c).conjTranspose -
    (starRingEnd ℂ (hcProduct Θ a b c) / frobNormSq (Θ.A a)) • Θ.A a

/-- Δ^(B)_abc = (C_c A_a)† - (T*_abc / ‖B_b‖²) B_b -/
def misalignmentResidualB (Θ : HCParams n) (a b c : Fin n) :
    Matrix (Fin n) (Fin n) ℂ :=
  (Θ.C c * Θ.A a).conjTranspose -
    (starRingEnd ℂ (hcProduct Θ a b c) / frobNormSq (Θ.B b)) • Θ.B b

/-- Δ^(C)_abc = (A_a B_b)† - (T*_abc / ‖C_c‖²) C_c -/
def misalignmentResidualC (Θ : HCParams n) (a b c : Fin n) :
    Matrix (Fin n) (Fin n) ℂ :=
  (Θ.A a * Θ.B b).conjTranspose -
    (starRingEnd ℂ (hcProduct Θ a b c) / frobNormSq (Θ.C c)) • Θ.C c

/-- Helper: frobInner distributes over subtraction on the right. -/
theorem frobInner_sub (X Y Z : Matrix (Fin n) (Fin n) ℂ) :
    frobInner X (Y - Z) = frobInner X Y - frobInner X Z := by
  simp only [frobInner, Matrix.mul_sub, Matrix.trace_sub, mul_sub]

/-- Helper: frobInner distributes over scalar multiplication on the right. -/
theorem frobInner_smul (X : Matrix (Fin n) (Fin n) ℂ)
    (r : ℂ) (Y : Matrix (Fin n) (Fin n) ℂ) :
    frobInner X (r • Y) = r * frobInner X Y := by
  unfold frobInner
  rw [show X.conjTranspose * (r • Y) = r • (X.conjTranspose * Y)
      from Algebra.mul_smul_comm r X.conjTranspose Y]
  rw [Matrix.trace_smul, smul_eq_mul, mul_left_comm]

/-- Helper: frobInner (A) (A) = frobNormSq (A). -/
theorem frobInner_self (X : Matrix (Fin n) (Fin n) ℂ) :
    frobInner X X = frobNormSq X := rfl

/-- Helper: frobInner distributes over addition on the right. -/
theorem frobInner_add_right (X Y Z : Matrix (Fin n) (Fin n) ℂ) :
    frobInner X (Y + Z) = frobInner X Y + frobInner X Z := by
  simp only [frobInner, Matrix.mul_add, Matrix.trace_add, mul_add]

/-- Helper: frobInner distributes over subtraction on the left. -/
theorem frobInner_sub_left (X Y Z : Matrix (Fin n) (Fin n) ℂ) :
    frobInner (X - Y) Z = frobInner X Z - frobInner Y Z := by
  unfold frobInner
  rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.trace_sub, mul_sub]

/-- Helper: frobInner distributes over addition on the left. -/
theorem frobInner_add_left (X Y Z : Matrix (Fin n) (Fin n) ℂ) :
    frobInner (X + Y) Z = frobInner X Z + frobInner Y Z := by
  unfold frobInner
  rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.trace_add, mul_add]

/-- Helper: frobInner distributes over scalar multiplication on the left. -/
theorem frobInner_smul_left (r : ℂ) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    frobInner (r • X) Y = starRingEnd ℂ r * frobInner X Y := by
  unfold frobInner
  rw [Matrix.conjTranspose_smul, smul_mul_assoc, Matrix.trace_smul, smul_eq_mul]
  simp only [starRingEnd_apply]
  rw [mul_left_comm]

/-- star(frobInner X Y) = frobInner Y X -/
theorem star_frobInner (X Y : Matrix (Fin n) (Fin n) ℂ) :
    starRingEnd ℂ (frobInner X Y) = frobInner Y X := by
  simp only [frobInner, starRingEnd_apply, star_mul']
  have h1 : star (1 / (n : ℂ)) = 1 / (n : ℂ) := by
    rw [star_div₀, star_one, star_natCast]
  have h2 : star (X.conjTranspose * Y).trace = (Y.conjTranspose * X).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
  rw [h1, h2]

/-- frobNormSq is invariant under conjTranspose. -/
theorem frobNormSq_conjTranspose (M : Matrix (Fin n) (Fin n) ℂ) :
    frobNormSq M.conjTranspose = frobNormSq M := by
  unfold frobNormSq frobInner
  rw [Matrix.conjTranspose_conjTranspose]
  congr 1
  exact Matrix.trace_mul_comm M M.conjTranspose

/-- Pythagoras: if ⟨U, V⟩ = 0 then ‖U + V‖² = ‖U‖² + ‖V‖². -/
theorem frobNormSq_add_of_orthog (U V : Matrix (Fin n) (Fin n) ℂ)
    (h : frobInner U V = 0) :
    frobNormSq (U + V) = frobNormSq U + frobNormSq V := by
  have h' : frobInner V U = 0 := by
    rw [← star_frobInner, h, map_zero]
  show frobInner (U + V) (U + V) = frobInner U U + frobInner V V
  rw [frobInner_add_left, frobInner_add_right, frobInner_add_right, h, h']
  ring

/-- frobNormSq of a scalar multiple. -/
theorem frobNormSq_smul (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    frobNormSq (c • X) = c * starRingEnd ℂ c * frobNormSq X := by
  show frobInner (c • X) (c • X) = c * starRingEnd ℂ c * frobInner X X
  rw [frobInner_smul_left, frobInner_smul]
  ring

/-- Helper: star(frobNormSq X) = frobNormSq X (since it's real). -/
theorem star_frobNormSq (X : Matrix (Fin n) (Fin n) ℂ) :
    star (frobNormSq X) = frobNormSq X := by
  have him := frobNormSq_real X
  apply Complex.ext
  · simp [Complex.star_def, Complex.conj_re]
  · simp [Complex.star_def, Complex.conj_im, him]

/-! ## Definiteness of frobNormSq -/

/-- Helper: frobNormSq 0 = 0. -/
private theorem frobNormSq_zero' : frobNormSq (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  unfold frobNormSq frobInner
  simp [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.trace_zero, mul_zero]

/-- frobNormSq X = 0 ↔ X = 0. -/
private theorem frobNormSq_eq_zero_iff' (X : Matrix (Fin n) (Fin n) ℂ) :
    frobNormSq X = 0 ↔ X = 0 := by
  constructor
  · intro h
    unfold frobNormSq frobInner at h
    have hn : (1 / (n : ℂ)) ≠ 0 := by
      rw [one_div]; exact inv_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne n))
    have htrace := (mul_eq_zero.mp h).resolve_left hn
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
        Matrix.conjTranspose_apply] at htrace
    ext i j
    show X i j = (0 : Matrix (Fin n) (Fin n) ℂ) i j
    simp only [Matrix.zero_apply]
    by_contra hne
    have hpos : (0 : ℝ) < Complex.normSq (X i j) := Complex.normSq_pos.mpr hne
    have hterm_nonneg : ∀ k l : Fin n,
        0 ≤ (star (X l k) * X l k).re := by
      intro k l
      simp only [← starRingEnd_apply, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
      exact Complex.normSq_nonneg _
    have hsum_re_eq : ∑ k : Fin n, ∑ l : Fin n,
        (star (X l k) * X l k).re = 0 := by
      have h0 : (∑ x : Fin n, ∑ x_1 : Fin n, star (X x_1 x) * X x_1 x).re = 0 := by
        rw [htrace]; rfl
      conv at h0 => lhs; rw [show (∑ x : Fin n, ∑ x_1 : Fin n,
        star (X x_1 x) * X x_1 x).re = ∑ x : Fin n, ∑ x_1 : Fin n,
        (star (X x_1 x) * X x_1 x).re from by simp [map_sum, Complex.add_re]]
      exact h0
    have h_term_pos : 0 < (star (X i j) * X i j).re := by
      simp only [← starRingEnd_apply, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
      exact hpos
    have h_inner_le : (star (X i j) * X i j).re ≤
        ∑ l : Fin n, (star (X l j) * X l j).re :=
      Finset.single_le_sum (fun l _ => hterm_nonneg j l) (Finset.mem_univ i)
    have h_outer_le : ∑ l : Fin n, (star (X l j) * X l j).re ≤
        ∑ k : Fin n, ∑ l : Fin n, (star (X l k) * X l k).re :=
      Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => hterm_nonneg k l))
        (Finset.mem_univ j)
    linarith
  · intro h; rw [h, frobNormSq_zero']

/-! ## Cauchy-Schwarz for frobInner -/

/-- General Cauchy-Schwarz inequality for the normalized Frobenius inner product:
    |⟨X, Y⟩|² ≤ ‖X‖² · ‖Y‖².
    Proof: set p = ⟨X,Y⟩, q = ‖Y‖² (real), expand 0 ≤ ‖q·X - p*·Y‖².re
    to obtain q.re² · ‖X‖².re - q.re · |p|² ≥ 0, then divide by q.re. -/
private theorem frobInner_cauchy_schwarz
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    Complex.normSq (frobInner X Y) ≤
      (frobNormSq X).re * (frobNormSq Y).re := by
  set p := frobInner X Y with hp_def
  set q := frobNormSq Y with hq_def
  have hq_im : q.im = 0 := frobNormSq_real Y
  have hq_re_nonneg : (0 : ℝ) ≤ q.re := frobNormSq_nonneg Y
  -- starRingEnd ℂ q = q because q is self-adjoint (real)
  have hq_star : starRingEnd ℂ q = q := by
    simp only [starRingEnd_apply]; exact star_frobNormSq Y
  -- sp = starRingEnd ℂ p (= conj p)
  set sp := starRingEnd ℂ p with hsp_def
  -- sp * p = ↑(normSq p)  since sp = conj p and conj(p)*p = |p|²
  have hsp_p : sp * p = ↑(Complex.normSq p) := by
    simp only [hsp_def, starRingEnd_apply]
    -- star p * p = normSq p as complex number
    -- Use: normSq p = p.re^2 + p.im^2, and star p = ⟨p.re, -p.im⟩
    apply Complex.ext
    · -- Real part: p.re * p.re + p.im * p.im = p.re^2 + p.im^2
      simp only [Complex.mul_re, Complex.normSq_apply, Complex.ofReal_re]
      have hstar_re : (star p).re = p.re := by simp [Complex.star_def]
      have hstar_im : (star p).im = -p.im := by simp [Complex.star_def]
      rw [hstar_re, hstar_im]; ring
    · -- Imaginary part: 0
      simp only [Complex.mul_im, Complex.normSq_apply, Complex.ofReal_im]
      have hstar_re : (star p).re = p.re := by simp [Complex.star_def]
      have hstar_im : (star p).im = -p.im := by simp [Complex.star_def]
      rw [hstar_re, hstar_im]; ring
  -- p * sp = ↑(normSq p)
  have hp_sp : p * sp = ↑(Complex.normSq p) := by
    rw [mul_comm]; exact hsp_p
  -- The nonnegativity witness
  have hnn : (frobNormSq (q • X - sp • Y)).re ≥ 0 := frobNormSq_nonneg _
  -- Helper: .re of a ℝ-cast is the original real
  have ofReal_re : ∀ r : ℝ, (↑r : ℂ).re = r := Complex.ofReal_re
  have ofReal_im : ∀ r : ℝ, (↑r : ℂ).im = 0 := Complex.ofReal_im
  -- Term 1: (frobNormSq (q • X)).re = q.re² · (frobNormSq X).re
  have hterm1_re : (frobNormSq (q • X)).re = q.re ^ 2 * (frobNormSq X).re := by
    rw [frobNormSq_smul, hq_star]
    simp only [Complex.mul_re, hq_im, frobNormSq_real X]
    ring
  -- Term 2: (frobInner (q•X) (sp•Y)).re = q.re · normSq p
  -- frobInner(q•X)(sp•Y) = sp * (starRingEnd q * p) = sp * q * p  (using hq_star)
  have hterm2_re : (frobInner (q • X) (sp • Y)).re = q.re * Complex.normSq p := by
    rw [frobInner_smul (q • X) sp Y, frobInner_smul_left q X Y, hq_star]
    -- goal: (sp * (q * p)).re = q.re * normSq p
    rw [show sp * (q * p) = sp * p * q from by ring, hsp_p]
    -- goal: (↑(normSq p) * q).re = q.re * normSq p
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hq_im]
    ring
  -- Term 3: (frobInner (sp•Y) (q•X)).re = q.re · normSq p
  -- frobInner(sp•Y)(q•X) = q * (starRingEnd(sp) * frobInner Y X)
  --   = q * (p * sp)  since starRingEnd(sp) = p and frobInner Y X = sp
  have hsp_star : starRingEnd ℂ sp = p := by
    simp only [hsp_def, map_star, starRingEnd_apply, star_star]
  have hfrobYX : frobInner Y X = sp := by
    rw [← star_frobInner X Y, ← hp_def, hsp_def]
  have hterm3_re : (frobInner (sp • Y) (q • X)).re = q.re * Complex.normSq p := by
    rw [frobInner_smul (sp • Y) q X, frobInner_smul_left sp Y X, hsp_star, hfrobYX]
    -- goal: (q * (p * sp)).re = q.re * normSq p
    rw [show q * (p * sp) = p * sp * q from by ring, hp_sp]
    -- goal: (↑(normSq p) * q).re = q.re * normSq p
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hq_im]
    ring
  -- Term 4: (frobNormSq (sp • Y)).re = normSq p · q.re
  -- frobNormSq(sp•Y) = sp * starRingEnd(sp) * frobNormSq Y = sp * p * q = ↑(normSq p) * q
  have hterm4_re : (frobNormSq (sp • Y)).re = Complex.normSq p * q.re := by
    rw [frobNormSq_smul, hsp_star, hsp_p]
    -- goal: (↑(normSq p) * q).re = normSq p * q.re
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hq_im]
    ring
  -- Combine via the sub expansion
  have hkey : (frobNormSq (q • X - sp • Y)).re =
      q.re ^ 2 * (frobNormSq X).re - q.re * Complex.normSq p := by
    show (frobInner (q • X - sp • Y) (q • X - sp • Y)).re = _
    rw [frobInner_sub_left, frobInner_sub, frobInner_sub]
    simp only [Complex.sub_re, Complex.add_re]
    rw [show (frobInner (q • X) (q • X)).re = (frobNormSq (q • X)).re from rfl,
        show (frobInner (sp • Y) (sp • Y)).re = (frobNormSq (sp • Y)).re from rfl]
    rw [hterm1_re, hterm2_re, hterm3_re, hterm4_re]
    ring
  rw [hkey] at hnn
  -- hnn : q.re² · ‖X‖².re - q.re · normSq p ≥ 0
  -- Case split on q.re = 0 or q.re > 0
  rcases hq_re_nonneg.lt_or_eq with hq_pos | hq_zero
  · -- q.re > 0: from hnn, q.re · ‖X‖².re ≥ normSq p
    nlinarith [Complex.normSq_nonneg p, frobNormSq_nonneg X, sq_nonneg q.re]
  · -- q.re = 0: Y = 0 (since frobNormSq Y has .re = 0 and .im = 0)
    have hY_zero : Y = 0 := by
      rw [← frobNormSq_eq_zero_iff']
      apply Complex.ext
      · rw [← hq_def]; exact hq_zero.symm
      · rw [← hq_def]; exact hq_im
    -- p = frobInner X Y = 0, so normSq p = 0
    have hp0 : p = 0 := by rw [hp_def, hY_zero]; simp [frobInner, Matrix.mul_zero, mul_zero]
    -- Goal: normSq p ≤ (frobNormSq X).re * q.re
    rw [hp0, Complex.normSq_zero, hq_zero.symm, mul_zero]

/-- The Cauchy-Schwarz bound: |T_abc|² ≤ ‖A_a‖² · ‖B_b C_c‖²
    (since T_abc = ⟨A_a†, B_b C_c⟩ and ‖A_a†‖² = ‖A_a‖²). -/
theorem cauchySchwarz_jacobian (Θ : HCParams n) (a b c : Fin n) :
    Complex.normSq (hcProduct Θ a b c) ≤
      (frobNormSq (Θ.A a)).re * (frobNormSq (Θ.B b * Θ.C c)).re := by
  rw [hcProduct_eq_frobInner, ← frobNormSq_conjTranspose (Θ.A a)]
  exact frobInner_cauchy_schwarz (Θ.A a).conjTranspose (Θ.B b * Θ.C c)

/-- The local lower bound on the Jacobian norm:
    ‖B_b C_c‖² ≥ |T_abc|² / ‖A_a‖². -/
theorem jacobian_lower_bound (Θ : HCParams n) (hnd : Nondegenerate Θ)
    (a b c : Fin n) :
    (frobNormSq (Θ.B b * Θ.C c)).re ≥
      Complex.normSq (hcProduct Θ a b c) / (frobNormSq (Θ.A a)).re := by
  have hCS := cauchySchwarz_jacobian Θ a b c
  have hA_re_pos : 0 < (frobNormSq (Θ.A a)).re := by
    rcases (frobNormSq_nonneg (Θ.A a)).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso; exact hnd.A_pos a (Complex.ext heq.symm (frobNormSq_real (Θ.A a)))
  rwa [ge_iff_le, div_le_iff₀ hA_re_pos, mul_comm]

/-- Tr(A† (BC)†) = star(Tr(ABC)).
    Uses trace cyclicity and Tr(M†) = star(Tr(M)). -/
theorem trace_conjTranspose_mul_conjTranspose
    (A B C : Matrix (Fin n) (Fin n) ℂ) :
    (A.conjTranspose * (B * C).conjTranspose).trace =
      starRingEnd ℂ ((A * B * C).trace) := by
  simp only [starRingEnd_apply]
  rw [Matrix.conjTranspose_mul B C]
  rw [← Matrix.trace_conjTranspose (A * B * C)]
  rw [Matrix.conjTranspose_mul (A * B) C, Matrix.conjTranspose_mul A B]
  -- LHS: (A† * (C† * B†)).trace, RHS: (C† * (B† * A†)).trace
  -- Rewrite RHS to left-assoc: (C† * B† * A†).trace
  rw [← Matrix.mul_assoc C.conjTranspose B.conjTranspose A.conjTranspose]
  exact Matrix.trace_mul_comm A.conjTranspose (C.conjTranspose * B.conjTranspose)

/-- Helper: frobInner A (BC)† = conj(hcProduct Θ a b c). -/
theorem frobInner_conjTranspose_eq_conj_hcProduct (Θ : HCParams n)
    (a b c : Fin n) :
    frobInner (Θ.A a) (Θ.B b * Θ.C c).conjTranspose =
      starRingEnd ℂ (hcProduct Θ a b c) := by
  simp only [frobInner, hcProduct, starRingEnd_apply, star_mul']
  congr 1
  · rw [star_div₀, star_one, star_natCast]
  · simp only [← starRingEnd_apply]
    exact trace_conjTranspose_mul_conjTranspose (Θ.A a) (Θ.B b) (Θ.C c)

/-- Helper: frobInner B (CA)† = conj(hcProduct Θ a b c). -/
theorem frobInner_B_conjTranspose_eq_conj_hcProduct (Θ : HCParams n)
    (a b c : Fin n) :
    frobInner (Θ.B b) (Θ.C c * Θ.A a).conjTranspose =
      starRingEnd ℂ (hcProduct Θ a b c) := by
  simp only [frobInner, hcProduct, starRingEnd_apply, star_mul']
  congr 1
  · rw [star_div₀, star_one, star_natCast]
  · -- Tr(B† (CA)†) = star(Tr(ABC))
    -- Use: frobInner_conjTranspose_eq_conj_hcProduct applied with cyclic permutation
    -- Direct calculation via trace_conjTranspose_mul_conjTranspose
    have h1 := trace_conjTranspose_mul_conjTranspose (Θ.B b) (Θ.C c) (Θ.A a)
    simp only [starRingEnd_apply] at h1
    rw [h1]
    congr 1
    -- Tr(BCA) = Tr(ABC)
    calc (Θ.B b * Θ.C c * Θ.A a).trace
        = (Θ.A a * (Θ.B b * Θ.C c)).trace :=
          Matrix.trace_mul_comm (Θ.B b * Θ.C c) (Θ.A a)
      _ = (Θ.A a * Θ.B b * Θ.C c).trace := by rw [Matrix.mul_assoc]

/-- Helper: frobInner C (AB)† = conj(hcProduct Θ a b c). -/
theorem frobInner_C_conjTranspose_eq_conj_hcProduct (Θ : HCParams n)
    (a b c : Fin n) :
    frobInner (Θ.C c) (Θ.A a * Θ.B b).conjTranspose =
      starRingEnd ℂ (hcProduct Θ a b c) := by
  simp only [frobInner, hcProduct, starRingEnd_apply, star_mul']
  congr 1
  · rw [star_div₀, star_one, star_natCast]
  · -- Tr(C† (AB)†) = star(Tr(ABC))
    have h1 := trace_conjTranspose_mul_conjTranspose (Θ.C c) (Θ.A a) (Θ.B b)
    simp only [starRingEnd_apply] at h1
    rw [h1]
    congr 1
    calc (Θ.C c * Θ.A a * Θ.B b).trace
        = (Θ.B b * (Θ.C c * Θ.A a)).trace :=
          Matrix.trace_mul_comm (Θ.C c * Θ.A a) (Θ.B b)
      _ = (Θ.B b * Θ.C c * Θ.A a).trace := by rw [Matrix.mul_assoc]
      _ = (Θ.A a * (Θ.B b * Θ.C c)).trace :=
          Matrix.trace_mul_comm (Θ.B b * Θ.C c) (Θ.A a)
      _ = (Θ.A a * Θ.B b * Θ.C c).trace := by rw [Matrix.mul_assoc]

/-- Orthogonality: ⟨A_a, Δ^(A)_abc⟩ = 0. -/
theorem misalignmentResidualA_orthog (Θ : HCParams n) (hnd : Nondegenerate Θ)
    (a b c : Fin n) :
    frobInner (Θ.A a) (misalignmentResidualA Θ a b c) = 0 := by
  simp only [misalignmentResidualA]
  rw [frobInner_sub, frobInner_smul, frobInner_self]
  rw [frobInner_conjTranspose_eq_conj_hcProduct]
  have hne : frobNormSq (Θ.A a) ≠ 0 := hnd.A_pos a
  field_simp
  ring

/-- Orthogonality: ⟨B_b, Δ^(B)_abc⟩ = 0. -/
theorem misalignmentResidualB_orthog (Θ : HCParams n) (hnd : Nondegenerate Θ)
    (a b c : Fin n) :
    frobInner (Θ.B b) (misalignmentResidualB Θ a b c) = 0 := by
  simp only [misalignmentResidualB]
  rw [frobInner_sub, frobInner_smul, frobInner_self]
  rw [frobInner_B_conjTranspose_eq_conj_hcProduct]
  have hne : frobNormSq (Θ.B b) ≠ 0 := hnd.B_pos b
  field_simp
  ring

/-- Orthogonality: ⟨C_c, Δ^(C)_abc⟩ = 0. -/
theorem misalignmentResidualC_orthog (Θ : HCParams n) (hnd : Nondegenerate Θ)
    (a b c : Fin n) :
    frobInner (Θ.C c) (misalignmentResidualC Θ a b c) = 0 := by
  simp only [misalignmentResidualC]
  rw [frobInner_sub, frobInner_smul, frobInner_self]
  rw [frobInner_C_conjTranspose_eq_conj_hcProduct]
  have hne : frobNormSq (Θ.C c) ≠ 0 := hnd.C_pos c
  field_simp
  ring

/-- The misalignment penalty ℛ_δ(Θ) (Definition 4, Eq. 6):
    R = Σ δ_abc (‖Δ^(A)‖² + ‖Δ^(B)‖² + ‖Δ^(C)‖²). -/
def misalignmentPenalty (Θ : HCParams n) (f : BinOp n) : ℂ :=
  ∑ a : Fin n, ∑ b : Fin n,
    let c := f.op a b
    (frobNormSq (misalignmentResidualA Θ a b c) +
     frobNormSq (misalignmentResidualB Θ a b c) +
     frobNormSq (misalignmentResidualC Θ a b c))

/-- ℛ_δ(Θ) ≥ 0 (each term is a squared norm). -/
theorem misalignmentPenalty_nonneg (Θ : HCParams n) (f : BinOp n) :
    (misalignmentPenalty Θ f).re ≥ 0 := by
  unfold misalignmentPenalty
  -- Distribute .re through sums
  have hre : (∑ a : Fin n, ∑ b : Fin n,
    (frobNormSq (misalignmentResidualA Θ a b (f.op a b)) +
     frobNormSq (misalignmentResidualB Θ a b (f.op a b)) +
     frobNormSq (misalignmentResidualC Θ a b (f.op a b)))).re =
    ∑ a : Fin n, ∑ b : Fin n,
    ((frobNormSq (misalignmentResidualA Θ a b (f.op a b))).re +
     (frobNormSq (misalignmentResidualB Θ a b (f.op a b))).re +
     (frobNormSq (misalignmentResidualC Θ a b (f.op a b))).re) := by
    simp [map_sum, Complex.add_re]
  rw [hre]
  exact Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => by
    have h1 := frobNormSq_nonneg (misalignmentResidualA Θ a b (f.op a b))
    have h2 := frobNormSq_nonneg (misalignmentResidualB Θ a b (f.op a b))
    have h3 := frobNormSq_nonneg (misalignmentResidualC Θ a b (f.op a b))
    linarith))

/-! ## Lemma 1: Decomposition of ℋ -/

/-  **Lemma 1 (Decomposition of ℋ).**
    For any parameters Θ and target δ, the objective decomposes as
    ℋ(Θ) = ℬ_δ(Θ) + ℛ_δ(Θ).
    Consequently, ℋ(Θ) ≥ ℬ_δ(Θ), with equality iff ℛ_δ(Θ) = 0.

    Proof sketch:
    Rearrange Δ^(A) to express (B_b C_c)† = (T*_abc/‖A_a‖²) A_a + Δ^(A)_abc.
    By orthogonality ⟨A_a, Δ^(A)⟩ = 0, squaring the norm yields:
    ‖B_b C_c‖² = |T_abc|²/‖A_a‖² + ‖Δ^(A)‖².
    Aggregating over the three Jacobian terms gives H = B + R. -/

/-- Pythagoras for factor A: ‖BC‖² = |T|²/‖A‖² + ‖Δ^A‖². -/
private theorem pythagoras_A (Θ : HCParams n) (f : BinOp n) (hnd : Nondegenerate Θ)
    (a b : Fin n) :
    frobNormSq (Θ.B b * Θ.C (f.op a b)) =
      hcProduct Θ a b (f.op a b) * starRingEnd ℂ (hcProduct Θ a b (f.op a b)) /
        frobNormSq (Θ.A a) +
      frobNormSq (misalignmentResidualA Θ a b (f.op a b)) := by
  set c := f.op a b
  set t := hcProduct Θ a b c
  set nA := frobNormSq (Θ.A a)
  set proj := (starRingEnd ℂ t / nA) • Θ.A a
  set ΔA := misalignmentResidualA Θ a b c
  -- Step 1: (BC)† = proj + ΔA
  have decomp : (Θ.B b * Θ.C c).conjTranspose = proj + ΔA := by
    change _ = proj + ((Θ.B b * Θ.C c).conjTranspose - proj)
    abel
  -- Step 2: frobNormSq(BC) = frobNormSq((BC)†)
  rw [← frobNormSq_conjTranspose (Θ.B b * Θ.C c)]
  -- Step 3: rewrite (BC)† as proj + ΔA, apply Pythagoras
  rw [decomp]
  have orthog : frobInner proj ΔA = 0 := by
    show frobInner ((starRingEnd ℂ t / nA) • Θ.A a) ΔA = 0
    rw [frobInner_smul_left, misalignmentResidualA_orthog Θ hnd a b c, mul_zero]
  rw [frobNormSq_add_of_orthog proj ΔA orthog]
  -- Step 4: compute frobNormSq(proj) = t * star t / nA
  congr 1
  show frobNormSq ((starRingEnd ℂ t / nA) • Θ.A a) = t * starRingEnd ℂ t / nA
  rw [frobNormSq_smul]
  have hne : nA ≠ 0 := hnd.A_pos a
  have hstar_nA : star nA = nA := star_frobNormSq (Θ.A a)
  simp only [starRingEnd_apply, star_div₀, star_star, hstar_nA]
  field_simp
  ring

/-- Pythagoras for factor B: ‖CA‖² = |T|²/‖B‖² + ‖Δ^B‖². -/
private theorem pythagoras_B (Θ : HCParams n) (f : BinOp n) (hnd : Nondegenerate Θ)
    (a b : Fin n) :
    frobNormSq (Θ.C (f.op a b) * Θ.A a) =
      hcProduct Θ a b (f.op a b) * starRingEnd ℂ (hcProduct Θ a b (f.op a b)) /
        frobNormSq (Θ.B b) +
      frobNormSq (misalignmentResidualB Θ a b (f.op a b)) := by
  set c := f.op a b
  set t := hcProduct Θ a b c
  set nB := frobNormSq (Θ.B b)
  set proj := (starRingEnd ℂ t / nB) • Θ.B b
  set ΔB := misalignmentResidualB Θ a b c
  have decomp : (Θ.C c * Θ.A a).conjTranspose = proj + ΔB := by
    change _ = proj + ((Θ.C c * Θ.A a).conjTranspose - proj)
    abel
  rw [← frobNormSq_conjTranspose (Θ.C c * Θ.A a), decomp]
  have orthog : frobInner proj ΔB = 0 := by
    show frobInner ((starRingEnd ℂ t / nB) • Θ.B b) ΔB = 0
    rw [frobInner_smul_left, misalignmentResidualB_orthog Θ hnd a b c, mul_zero]
  rw [frobNormSq_add_of_orthog proj ΔB orthog]
  congr 1
  show frobNormSq ((starRingEnd ℂ t / nB) • Θ.B b) = t * starRingEnd ℂ t / nB
  rw [frobNormSq_smul]
  have hne : nB ≠ 0 := hnd.B_pos b
  have hstar_nB : star nB = nB := star_frobNormSq (Θ.B b)
  simp only [starRingEnd_apply, star_div₀, star_star, hstar_nB]
  field_simp
  ring

/-- Pythagoras for factor C: ‖AB‖² = |T|²/‖C‖² + ‖Δ^C‖². -/
private theorem pythagoras_C (Θ : HCParams n) (f : BinOp n) (hnd : Nondegenerate Θ)
    (a b : Fin n) :
    frobNormSq (Θ.A a * Θ.B b) =
      hcProduct Θ a b (f.op a b) * starRingEnd ℂ (hcProduct Θ a b (f.op a b)) /
        frobNormSq (Θ.C (f.op a b)) +
      frobNormSq (misalignmentResidualC Θ a b (f.op a b)) := by
  set c := f.op a b
  set t := hcProduct Θ a b c
  set nC := frobNormSq (Θ.C c)
  set proj := (starRingEnd ℂ t / nC) • Θ.C c
  set ΔC := misalignmentResidualC Θ a b c
  have decomp : (Θ.A a * Θ.B b).conjTranspose = proj + ΔC := by
    change _ = proj + ((Θ.A a * Θ.B b).conjTranspose - proj)
    abel
  rw [← frobNormSq_conjTranspose (Θ.A a * Θ.B b), decomp]
  have orthog : frobInner proj ΔC = 0 := by
    show frobInner ((starRingEnd ℂ t / nC) • Θ.C c) ΔC = 0
    rw [frobInner_smul_left, misalignmentResidualC_orthog Θ hnd a b c, mul_zero]
  rw [frobNormSq_add_of_orthog proj ΔC orthog]
  congr 1
  show frobNormSq ((starRingEnd ℂ t / nC) • Θ.C c) = t * starRingEnd ℂ t / nC
  rw [frobNormSq_smul]
  have hne : nC ≠ 0 := hnd.C_pos c
  have hstar_nC : star nC = nC := star_frobNormSq (Θ.C c)
  simp only [starRingEnd_apply, star_div₀, star_star, hstar_nC]
  field_simp
  ring

theorem lemma1_decomposition (Θ : HCParams n) (f : BinOp n) (hnd : Nondegenerate Θ) :
    objective Θ f = inverseScalePenalty Θ f + misalignmentPenalty Θ f := by
  -- Reduce objective to sum over support
  rw [objective_eq_sum_support]
  -- Combine the RHS sums
  simp only [inverseScalePenalty, misalignmentPenalty]
  rw [← Finset.sum_add_distrib]
  congr 1; ext a
  rw [← Finset.sum_add_distrib]
  congr 1; ext b
  -- For each (a, b): use the three Pythagoras identities
  set c := f.op a b with hc
  set t := hcProduct Θ a b c with ht
  rw [pythagoras_A Θ f hnd a b, pythagoras_B Θ f hnd a b, pythagoras_C Θ f hnd a b]
  ring

/-- ℋ(Θ) ≥ ℬ_δ(Θ), with equality iff R = 0 (perfect collinearity). -/
theorem lemma1_objective_ge_inverseScalePenalty (Θ : HCParams n) (f : BinOp n)
    (hnd : Nondegenerate Θ) :
    (objective Θ f).re ≥ (inverseScalePenalty Θ f).re := by
  have hdecomp := decomposition Θ f hnd
  have hRnonneg := misalignmentPenalty_nonneg Θ f
  rw [hdecomp]
  simp only [Complex.add_re]
  linarith

/-! ## Perfect collinearity (R = 0) -/

/-- Perfect collinearity: ℛ_δ(Θ) = 0.
    Equivalent to the collinear identities (Eq. 7):
    B_b C_c = T_abc (A_a† / ‖A_a‖²), etc. -/
def PerfectCollinearity (Θ : HCParams n) (f : BinOp n) : Prop :=
  misalignmentPenalty Θ f = 0

/-- The collinear identities (Eq. 7). -/
structure CollinearIdentities (Θ : HCParams n) (f : BinOp n) : Prop where
  idA : ∀ a b : Fin n,
    let c := f.op a b
    Θ.B b * Θ.C c = (hcProduct Θ a b c / frobNormSq (Θ.A a)) • (Θ.A a).conjTranspose
  idB : ∀ a b : Fin n,
    let c := f.op a b
    Θ.C c * Θ.A a = (hcProduct Θ a b c / frobNormSq (Θ.B b)) • (Θ.B b).conjTranspose
  idC : ∀ a b : Fin n,
    let c := f.op a b
    Θ.A a * Θ.B b = (hcProduct Θ a b c / frobNormSq (Θ.C c)) • (Θ.C c).conjTranspose

/-- Helper: conjTranspose of the collinear identity gives the residual equation. -/
theorem collinearA_implies_residualA_zero (Θ : HCParams n) (hnd : Nondegenerate Θ)
    (a b c : Fin n)
    (hid : Θ.B b * Θ.C c = (hcProduct Θ a b c / frobNormSq (Θ.A a)) •
      (Θ.A a).conjTranspose) :
    misalignmentResidualA Θ a b c = 0 := by
  simp only [misalignmentResidualA]
  rw [hid, Matrix.conjTranspose_smul, Matrix.conjTranspose_conjTranspose]
  -- Goal: star(T/‖A‖²) • A - (T*/‖A‖²) • A = 0
  rw [sub_eq_zero]
  congr 1
  -- Need: star(hcProduct / frobNormSq) = starRingEnd ℂ hcProduct / frobNormSq
  rw [star_div₀, starRingEnd_apply, star_frobNormSq]

/-- Helper: similar for B residual. -/
theorem collinearB_implies_residualB_zero (Θ : HCParams n) (hnd : Nondegenerate Θ)
    (a b c : Fin n)
    (hid : Θ.C c * Θ.A a = (hcProduct Θ a b c / frobNormSq (Θ.B b)) •
      (Θ.B b).conjTranspose) :
    misalignmentResidualB Θ a b c = 0 := by
  simp only [misalignmentResidualB]
  rw [hid, Matrix.conjTranspose_smul, Matrix.conjTranspose_conjTranspose]
  rw [sub_eq_zero]
  congr 1
  rw [star_div₀, starRingEnd_apply, star_frobNormSq]

/-- Helper: similar for C residual. -/
theorem collinearC_implies_residualC_zero (Θ : HCParams n) (hnd : Nondegenerate Θ)
    (a b c : Fin n)
    (hid : Θ.A a * Θ.B b = (hcProduct Θ a b c / frobNormSq (Θ.C c)) •
      (Θ.C c).conjTranspose) :
    misalignmentResidualC Θ a b c = 0 := by
  simp only [misalignmentResidualC]
  rw [hid, Matrix.conjTranspose_smul, Matrix.conjTranspose_conjTranspose]
  rw [sub_eq_zero]
  congr 1
  rw [star_div₀, starRingEnd_apply, star_frobNormSq]

/-- Helper: frobNormSq 0 = 0. -/
theorem frobNormSq_zero : frobNormSq (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  unfold frobNormSq frobInner
  simp [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.trace_zero, mul_zero]

/-- Definiteness: frobNormSq X = 0 ↔ X = 0. -/
theorem frobNormSq_eq_zero_iff (X : Matrix (Fin n) (Fin n) ℂ) :
    frobNormSq X = 0 ↔ X = 0 := by
  constructor
  · intro h
    unfold frobNormSq frobInner at h
    have hn : (1 / (n : ℂ)) ≠ 0 := by
      rw [one_div]; exact inv_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne n))
    have htrace := (mul_eq_zero.mp h).resolve_left hn
    -- Tr(X† X) = Σ_{i,j} |X_{ji}|² = 0
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
        Matrix.conjTranspose_apply] at htrace
    -- htrace : ∑ x, ∑ x_1, star (X x_1 x) * X x_1 x = 0
    ext i j
    show X i j = (0 : Matrix (Fin n) (Fin n) ℂ) i j
    simp only [Matrix.zero_apply]
    by_contra hne
    -- |X i j|² > 0
    have hpos : (0 : ℝ) < Complex.normSq (X i j) := Complex.normSq_pos.mpr hne
    -- Each term star(z)*z is a nonneg real number
    -- Convert everything to real sums using map_sum
    have hterm_nonneg : ∀ k l : Fin n,
        0 ≤ (star (X l k) * X l k).re := by
      intro k l
      simp only [← starRingEnd_apply, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
      exact Complex.normSq_nonneg _
    -- The sum of nonneg .re terms is 0
    have hsum_re_eq : ∑ k : Fin n, ∑ l : Fin n,
        (star (X l k) * X l k).re = 0 := by
      have h0 : (∑ x : Fin n, ∑ x_1 : Fin n, star (X x_1 x) * X x_1 x).re = 0 := by
        rw [htrace]; rfl
      -- Distribute .re through sums explicitly
      conv at h0 => lhs; rw [show (∑ x : Fin n, ∑ x_1 : Fin n,
        star (X x_1 x) * X x_1 x).re = ∑ x : Fin n, ∑ x_1 : Fin n,
        (star (X x_1 x) * X x_1 x).re from by simp [map_sum, Complex.add_re]]
      exact h0
    -- The (j,i)-th term has positive re
    have h_term_pos : 0 < (star (X i j) * X i j).re := by
      simp only [← starRingEnd_apply, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
      exact hpos
    -- Extract: term ≤ inner sum ≤ outer sum = 0
    have h_inner_le : (star (X i j) * X i j).re ≤
        ∑ l : Fin n, (star (X l j) * X l j).re :=
      Finset.single_le_sum (fun l _ => hterm_nonneg j l) (Finset.mem_univ i)
    have h_outer_le : ∑ l : Fin n, (star (X l j) * X l j).re ≤
        ∑ k : Fin n, ∑ l : Fin n, (star (X l k) * X l k).re :=
      Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => hterm_nonneg k l))
        (Finset.mem_univ j)
    linarith
  · intro h; rw [h, frobNormSq_zero]

/-- Helper: misalignmentPenalty = 0 implies each residual is zero. -/
private theorem misalignmentPenalty_zero_implies_residuals_zero
    (Θ : HCParams n) (f : BinOp n) (hR : misalignmentPenalty Θ f = 0)
    (a b : Fin n) :
    misalignmentResidualA Θ a b (f.op a b) = 0 ∧
    misalignmentResidualB Θ a b (f.op a b) = 0 ∧
    misalignmentResidualC Θ a b (f.op a b) = 0 := by
  -- Each frobNormSq has nonneg re and zero im
  have hR_re : ∑ a' : Fin n, ∑ b' : Fin n,
      ((frobNormSq (misalignmentResidualA Θ a' b' (f.op a' b'))).re +
       (frobNormSq (misalignmentResidualB Θ a' b' (f.op a' b'))).re +
       (frobNormSq (misalignmentResidualC Θ a' b' (f.op a' b'))).re) = 0 := by
    have h0 : (misalignmentPenalty Θ f).re = 0 := by rw [hR]; rfl
    simp only [misalignmentPenalty] at h0
    convert h0 using 1
    simp [map_sum, Complex.add_re]
  -- The double sum of nonneg terms = 0
  have hA_re := frobNormSq_nonneg (misalignmentResidualA Θ a b (f.op a b))
  have hB_re := frobNormSq_nonneg (misalignmentResidualB Θ a b (f.op a b))
  have hC_re := frobNormSq_nonneg (misalignmentResidualC Θ a b (f.op a b))
  -- Each inner sum ≥ 0
  have hinner_nonneg : ∀ a' : Fin n,
      (∑ b' : Fin n,
        ((frobNormSq (misalignmentResidualA Θ a' b' (f.op a' b'))).re +
         (frobNormSq (misalignmentResidualB Θ a' b' (f.op a' b'))).re +
         (frobNormSq (misalignmentResidualC Θ a' b' (f.op a' b'))).re)) ≥ 0 := by
    intro a'
    apply Finset.sum_nonneg; intro b' _
    have := frobNormSq_nonneg (misalignmentResidualA Θ a' b' (f.op a' b'))
    have := frobNormSq_nonneg (misalignmentResidualB Θ a' b' (f.op a' b'))
    have := frobNormSq_nonneg (misalignmentResidualC Θ a' b' (f.op a' b'))
    linarith
  -- Extract the a-th outer summand = 0
  have houter := Finset.single_le_sum (fun a' _ => hinner_nonneg a') (Finset.mem_univ a)
  have houter_zero : (∑ b' : Fin n,
      ((frobNormSq (misalignmentResidualA Θ a b' (f.op a b'))).re +
       (frobNormSq (misalignmentResidualB Θ a b' (f.op a b'))).re +
       (frobNormSq (misalignmentResidualC Θ a b' (f.op a b'))).re)) = 0 := by
      linarith [houter, hR_re, hinner_nonneg a]
  -- Each b-summand ≥ 0
  have hbsummand_nonneg : ∀ b' : Fin n,
      (frobNormSq (misalignmentResidualA Θ a b' (f.op a b'))).re +
      (frobNormSq (misalignmentResidualB Θ a b' (f.op a b'))).re +
      (frobNormSq (misalignmentResidualC Θ a b' (f.op a b'))).re ≥ 0 := by
    intro b'
    have := frobNormSq_nonneg (misalignmentResidualA Θ a b' (f.op a b'))
    have := frobNormSq_nonneg (misalignmentResidualB Θ a b' (f.op a b'))
    have := frobNormSq_nonneg (misalignmentResidualC Θ a b' (f.op a b'))
    linarith
  have hbinner := Finset.single_le_sum (fun b' _ => hbsummand_nonneg b') (Finset.mem_univ b)
  have hb_zero :
      (frobNormSq (misalignmentResidualA Θ a b (f.op a b))).re +
      (frobNormSq (misalignmentResidualB Θ a b (f.op a b))).re +
      (frobNormSq (misalignmentResidualC Θ a b (f.op a b))).re = 0 := by linarith
  -- Each component is 0
  have hA_zero : (frobNormSq (misalignmentResidualA Θ a b (f.op a b))).re = 0 := by linarith
  have hB_zero : (frobNormSq (misalignmentResidualB Θ a b (f.op a b))).re = 0 := by linarith
  have hC_zero : (frobNormSq (misalignmentResidualC Θ a b (f.op a b))).re = 0 := by linarith
  -- frobNormSq is real, so re = 0 ∧ im = 0 → frobNormSq = 0 → residual = 0
  have him_A := frobNormSq_real (misalignmentResidualA Θ a b (f.op a b))
  have him_B := frobNormSq_real (misalignmentResidualB Θ a b (f.op a b))
  have him_C := frobNormSq_real (misalignmentResidualC Θ a b (f.op a b))
  refine ⟨(frobNormSq_eq_zero_iff _).mp (Complex.ext hA_zero him_A),
          (frobNormSq_eq_zero_iff _).mp (Complex.ext hB_zero him_B),
          (frobNormSq_eq_zero_iff _).mp (Complex.ext hC_zero him_C)⟩

/-- Helper: if misalign residual A is 0, the collinear identity for A holds. -/
private theorem residualA_zero_implies_identityA (Θ : HCParams n) (hnd : Nondegenerate Θ)
    (a b c : Fin n) (h : misalignmentResidualA Θ a b c = 0) :
    Θ.B b * Θ.C c =
      (hcProduct Θ a b c / frobNormSq (Θ.A a)) • (Θ.A a).conjTranspose := by
  -- From h: (BC)† - (T*/‖A‖²) • A = 0, so (BC)† = (T*/‖A‖²) • A
  have heq : (Θ.B b * Θ.C c).conjTranspose = (starRingEnd ℂ (hcProduct Θ a b c) /
      frobNormSq (Θ.A a)) • Θ.A a := by
    have h' := h
    simp only [misalignmentResidualA, sub_eq_zero] at h'
    exact h'
  -- Take conjTranspose: BC = star(T*/‖A‖²) • A†
  have := congr_arg Matrix.conjTranspose heq
  rw [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_smul] at this
  rw [this]
  congr 1
  -- star(T* / ‖A‖²) = T / ‖A‖²
  rw [star_div₀, starRingEnd_apply, star_star, star_frobNormSq]

/-- Helper: similar for B residual. -/
private theorem residualB_zero_implies_identityB (Θ : HCParams n) (hnd : Nondegenerate Θ)
    (a b c : Fin n) (h : misalignmentResidualB Θ a b c = 0) :
    Θ.C c * Θ.A a =
      (hcProduct Θ a b c / frobNormSq (Θ.B b)) • (Θ.B b).conjTranspose := by
  have heq : (Θ.C c * Θ.A a).conjTranspose = (starRingEnd ℂ (hcProduct Θ a b c) /
      frobNormSq (Θ.B b)) • Θ.B b := by
    have h' := h
    simp only [misalignmentResidualB, sub_eq_zero] at h'
    exact h'
  have := congr_arg Matrix.conjTranspose heq
  rw [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_smul] at this
  rw [this]; congr 1
  rw [star_div₀, starRingEnd_apply, star_star, star_frobNormSq]

/-- Helper: similar for C residual. -/
private theorem residualC_zero_implies_identityC (Θ : HCParams n) (hnd : Nondegenerate Θ)
    (a b c : Fin n) (h : misalignmentResidualC Θ a b c = 0) :
    Θ.A a * Θ.B b =
      (hcProduct Θ a b c / frobNormSq (Θ.C c)) • (Θ.C c).conjTranspose := by
  have heq : (Θ.A a * Θ.B b).conjTranspose = (starRingEnd ℂ (hcProduct Θ a b c) /
      frobNormSq (Θ.C c)) • Θ.C c := by
    have h' := h
    simp only [misalignmentResidualC, sub_eq_zero] at h'
    exact h'
  have := congr_arg Matrix.conjTranspose heq
  rw [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_smul] at this
  rw [this]; congr 1
  rw [star_div₀, starRingEnd_apply, star_star, star_frobNormSq]

/-- Perfect collinearity is equivalent to the collinear identities. -/
theorem perfectCollinearity_iff_identities (Θ : HCParams n) (f : BinOp n)
    (hnd : Nondegenerate Θ) :
    PerfectCollinearity Θ f ↔ CollinearIdentities Θ f := by
  constructor
  · -- Forward: R = 0 → identities
    intro hR
    have key := misalignmentPenalty_zero_implies_residuals_zero Θ f hR
    exact ⟨fun a b => residualA_zero_implies_identityA Θ hnd a b _ (key a b).1,
           fun a b => residualB_zero_implies_identityB Θ hnd a b _ (key a b).2.1,
           fun a b => residualC_zero_implies_identityC Θ hnd a b _ (key a b).2.2⟩
  · -- Backward: identities → R = 0
    intro ⟨hidA, hidB, hidC⟩
    unfold PerfectCollinearity misalignmentPenalty
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    have hA := collinearA_implies_residualA_zero Θ hnd a b (f.op a b) (hidA a b)
    have hB := collinearB_implies_residualB_zero Θ hnd a b (f.op a b) (hidB a b)
    have hC := collinearC_implies_residualC_zero Θ hnd a b (f.op a b) (hidC a b)
    simp only [hA, hB, hC, frobNormSq_zero, add_zero]

/-- Feasibility implies nondegeneracy: if T = δ on support, no factor slice can be zero. -/
theorem factorizes_implies_nondegenerate (Θ : HCParams n) (f : BinOp n)
    (hq : IsQuasigroup f) (hfeas : Factorizes Θ f) :
    Nondegenerate Θ where
  A_pos := fun a h => by
    have hA := (frobNormSq_eq_zero_iff _).mp h
    have ⟨b⟩ : Nonempty (Fin n) := ⟨⟨0, NeZero.pos n⟩⟩
    have := hfeas a b (f.op a b)
    simp [structureTensor] at this
    rw [hcProduct, hA, Matrix.zero_mul, Matrix.zero_mul, Matrix.trace_zero, mul_zero] at this
    exact zero_ne_one this
  B_pos := fun b h => by
    have hB := (frobNormSq_eq_zero_iff _).mp h
    have ⟨a⟩ : Nonempty (Fin n) := ⟨⟨0, NeZero.pos n⟩⟩
    have := hfeas a b (f.op a b)
    simp [structureTensor] at this
    rw [hcProduct, show Θ.A a * Θ.B b = 0 from by rw [hB, Matrix.mul_zero],
        Matrix.zero_mul, Matrix.trace_zero, mul_zero] at this
    exact zero_ne_one this
  C_pos := fun c h => by
    have hC := (frobNormSq_eq_zero_iff _).mp h
    -- Need (a, b) with f.op a b = c. By surjectivity of f.op a (quasigroup).
    have ⟨a⟩ : Nonempty (Fin n) := ⟨⟨0, NeZero.pos n⟩⟩
    obtain ⟨b, hb⟩ := (hq.left_cancel a).2 c
    have := hfeas a b c
    rw [structureTensor, show f.op a b = c from hb, if_pos rfl] at this
    rw [hcProduct, hC, Matrix.mul_zero, Matrix.trace_zero, mul_zero] at this
    exact zero_ne_one this

end
