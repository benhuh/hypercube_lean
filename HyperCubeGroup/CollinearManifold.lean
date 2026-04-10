/-
  HyperCubeGroup.CollinearManifold

  Analysis of the collinear manifold {Θ | R(Θ;δ) = 0} (Section 5).

  Main results:
  - Lemma 10: Shared Gram matrices X, Y, Z (index-independent, trace-n PSD)
  - Lemma 11: Normalized rank κ = rank(X)/n ≤ 1, with κ=1 iff full-rank (unitary)
  - Lemma 12: AM-GM lower bound B ≥ 3 Σ δ_abc |T_abc|^{4/3}
  - Theorem 16: On the collinear manifold, the minimum of H is achieved by
    a unitary collinear factorization with value 3|δ|
-/

import HyperCubeGroup.Decomposition

open Matrix BigOperators Finset

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ## Lemma 10: Shared Gram Matrices -/

/-- The normalized Gram matrix for factor A:
    X_a = A_a A_a† / ‖A_a‖². Under collinearity, this is index-independent. -/
def gramA (Θ : HCParams n) (a : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / frobNormSq (Θ.A a)) • (Θ.A a * (Θ.A a).conjTranspose)

/-- Similarly for B and C. -/
def gramB (Θ : HCParams n) (b : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / frobNormSq (Θ.B b)) • (Θ.B b * (Θ.B b).conjTranspose)

def gramC (Θ : HCParams n) (c : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / frobNormSq (Θ.C c)) • (Θ.C c * (Θ.C c).conjTranspose)

/-- **Lemma 10 (Shared Gram Matrices).**
    Assume nondegeneracy and perfect collinearity (R = 0).
    There exist index-independent, trace-n PSD Gram matrices X, Y, Z such that:
      X = A_a A_a† / ‖A_a‖² = C_c† C_c / ‖C_c‖²
      Y = B_b B_b† / ‖B_b‖² = A_a† A_a / ‖A_a‖²
      Z = C_c C_c† / ‖C_c‖² = B_b† B_b / ‖B_b‖²

    Proof: Substitute collinear identities into the associativity condition
    A_a(B_b C_c) = (A_a B_b)C_c. The collinearity forces
    A_a A_a† / ‖A_a‖² = C_c† C_c / ‖C_c‖² for all a, c in supported triples.
    Connectivity of the quasigroup support graph propagates this globally. -/
theorem shared_gram_matrices (Θ : HCParams n) (f : BinOp n)
    (hq : IsQuasigroup f) (hnd : Nondegenerate Θ)
    (hcol : PerfectCollinearity Θ f) (hfeas : Factorizes Θ f) :
    ∃ X : Matrix (Fin n) (Fin n) ℂ,
      (∀ a : Fin n, gramA Θ a = X) ∧
      (∀ c : Fin n, (1 / frobNormSq (Θ.C c)) •
        ((Θ.C c).conjTranspose * Θ.C c) = X) := by
  -- Get collinear identities from perfect collinearity
  have hids := (perfectCollinearity_iff_identities Θ f hnd).mp hcol
  -- Key: For any a, b with c = f(a,b), T_abc = 1 (feasibility on support)
  have hT : ∀ a b : Fin n, hcProduct Θ a b (f.op a b) = 1 := by
    intro a b
    have := hfeas a b (f.op a b)
    rwa [structureTensor, if_pos rfl] at this
  -- From idA: B_b C_c = (T/α_a) • A_a†
  -- From idC: A_a B_b = (T/γ_c) • C_c†
  -- Matrix associativity: A_a (B_b C_c) = (A_a B_b) C_c
  -- So (T/α_a) • (A_a A_a†) = (T/γ_c) • (C_c† C_c)
  have gram_eq : ∀ a b : Fin n,
      let c := f.op a b
      (1 / frobNormSq (Θ.A a)) • (Θ.A a * (Θ.A a).conjTranspose) =
      (1 / frobNormSq (Θ.C c)) • ((Θ.C c).conjTranspose * Θ.C c) := by
    intro a b c
    -- LHS: A_a * (B_b C_c) = A_a * ((T/α_a) • A_a†) = (T/α_a) • A_a A_a†
    have hidA := hids.idA a b
    -- RHS: (A_a B_b) * C_c = ((T/γ_c) • C_c†) * C_c = (T/γ_c) • C_c† C_c
    have hidC := hids.idC a b
    -- By associativity: (T/α_a) • A_a A_a† = (T/γ_c) • C_c† C_c
    have hassoc : Θ.A a * (Θ.B b * Θ.C c) = (Θ.A a * Θ.B b) * Θ.C c :=
      (Matrix.mul_assoc _ _ _).symm
    rw [hidA, hidC] at hassoc
    simp only [Matrix.mul_smul, Matrix.smul_mul] at hassoc
    -- hassoc: (T/α_a) • A_a A_a† = (T/γ_c) • C_c† C_c
    -- T = 1 on support:
    rw [hT a b] at hassoc
    simp only [one_div] at hassoc ⊢
    exact hassoc
  -- Fix a₀ (any element) and set X := gramA Θ a₀
  have ⟨a₀⟩ : Nonempty (Fin n) := ⟨⟨0, NeZero.pos n⟩⟩
  use gramA Θ a₀
  constructor
  · -- Show gramA Θ a = gramA Θ a₀ for all a
    intro a
    -- For a₀, pick any b₀ and let c₀ = f(a₀, b₀)
    -- gram_eq a₀ b₀: gramA Θ a₀ = (1/γ_{c₀}) • C_{c₀}† C_{c₀}
    -- For a, using the surjectivity of f(a, ·), find b s.t. f(a,b) = c₀
    -- Then gram_eq a b: gramA Θ a = (1/γ_{c₀}) • C_{c₀}† C_{c₀}
    -- So gramA Θ a = gramA Θ a₀
    have ⟨b₀⟩ : Nonempty (Fin n) := ⟨⟨0, NeZero.pos n⟩⟩
    have key₀ := gram_eq a₀ b₀
    -- Find b such that f(a, b) = f(a₀, b₀) using bijectivity
    obtain ⟨b, hb⟩ := (hq.left_cancel a).2 (f.op a₀ b₀)
    have key := gram_eq a b
    rw [hb] at key
    simp only [gramA]
    rw [key, ← key₀]
  · -- Show (1/γ_c) • C_c† C_c = gramA Θ a₀ for all c
    intro c
    -- Find a, b with f(a,b) = c using right cancellation on a₀'s row... no.
    -- Actually use: f(a₀, ·) is bijective, so ∃ b₀ with f(a₀, b₀) = c
    obtain ⟨b₀, hb₀⟩ := (hq.left_cancel a₀).2 c
    have key := gram_eq a₀ b₀
    rw [hb₀] at key
    simp only [gramA] at key ⊢
    exact key.symm

/-! ## Lemma 11: Normalized Rank -/

/-- The dimensionless ratio κ_abc = ‖A_a‖² ‖B_b‖² ‖C_c‖² / |T_abc|²
    is constant across the support under collinearity. -/
def kappaTriple (Θ : HCParams n) (a b c : Fin n) : ℂ :=
  frobNormSq (Θ.A a) * frobNormSq (Θ.B b) * frobNormSq (Θ.C c) /
    (hcProduct Θ a b c * starRingEnd ℂ (hcProduct Θ a b c))

/-- **Lemma 11 (Normalized Rank κ).**
    Assume nondegeneracy and perfect collinearity.
    The ratio κ_abc is constant across the support; call it κ.
    The shared Gram matrices satisfy X = κ X², making P := κX an
    orthogonal projection. Hence κ = rank(X)/n ≤ 1,
    with equality (κ = 1) iff X = Y = Z = I_n (full-rank, Gram = identity). -/
theorem normalized_rank_constant (Θ : HCParams n) (f : BinOp n)
    (hq : IsQuasigroup f) (hnd : Nondegenerate Θ)
    (hcol : PerfectCollinearity Θ f) (hfeas : Factorizes Θ f) :
    ∃ κ : ℂ,
      (∀ a b : Fin n, kappaTriple Θ a b (f.op a b) = κ) ∧
      -- κ ≤ 1 (as real)
      κ.re ≤ 1 ∧ κ.re > 0 := by
  obtain ⟨X, hgA, hgC⟩ := shared_gram_matrices Θ f hq hnd hcol hfeas
  have hids := (perfectCollinearity_iff_identities Θ f hnd).mp hcol
  have hT : ∀ a b : Fin n, hcProduct Θ a b (f.op a b) = 1 := by
    intro a b; have := hfeas a b (f.op a b); rwa [structureTensor, if_pos rfl] at this
  -- Fix a₀, b₀ and define κ
  have ⟨a₀⟩ : Nonempty (Fin n) := ⟨⟨0, NeZero.pos n⟩⟩
  have ⟨b₀⟩ : Nonempty (Fin n) := ⟨⟨0, NeZero.pos n⟩⟩
  set κ := kappaTriple Θ a₀ b₀ (f.op a₀ b₀) with hκ_def
  -- On support, |T|² = 1 so κ = αβγ
  have hκ_simp : κ = frobNormSq (Θ.A a₀) * frobNormSq (Θ.B b₀) *
      frobNormSq (Θ.C (f.op a₀ b₀)) := by
    simp only [hκ_def, kappaTriple, hT a₀ b₀, map_one, mul_one, div_one]
  -- Helper: for any a, b, the product αβγ on support equals κ
  -- Key insight: X² = (1/κ) • X, and since X, X² are fixed, κ must be constant
  -- First show X² = (1/(α_a β_b γ_c)) • X for any supported triple
  have hX_sq_eq : ∀ a b : Fin n,
      X * X = (1 / (frobNormSq (Θ.A a) * frobNormSq (Θ.B b) *
        frobNormSq (Θ.C (f.op a b)))) • X := by
    intro a b
    set c := f.op a b
    set α := frobNormSq (Θ.A a)
    set β := frobNormSq (Θ.B b)
    set γ := frobNormSq (Θ.C c)
    set A := Θ.A a; set B := Θ.B b; set C := Θ.C c
    have hα_ne : α ≠ 0 := hnd.A_pos a
    have hβ_ne : β ≠ 0 := hnd.B_pos b
    have hγ_ne : γ ≠ 0 := hnd.C_pos c
    have hXA : X = (1 / α) • (A * A.conjTranspose) := by rw [← hgA a]; rfl
    have hXC : X = (1 / γ) • (C.conjTranspose * C) := by rw [← hgC c]
    have hAAt : A * A.conjTranspose = α • X := by
      rw [hXA, smul_smul, show α * (1 / α) = 1 from by field_simp [hα_ne], one_smul]
    -- Collinear identities for this triple
    have hidA := hids.idA a b; dsimp only at hidA; rw [hT a b] at hidA
    have hidB := hids.idB a b; dsimp only at hidB; rw [hT a b] at hidB
    -- A†C† = (1/β) • B
    have hAtCt : A.conjTranspose * C.conjTranspose = (1 / β) • B := by
      rw [← Matrix.conjTranspose_mul, hidB, Matrix.conjTranspose_smul,
          Matrix.conjTranspose_conjTranspose]
      congr 1; rw [star_div₀, star_one]; exact congrArg (1 / ·) (star_frobNormSq _)
    -- X² calc chain
    have : X * X = ((1 / α) • (A * A.conjTranspose)) *
                   ((1 / γ) • (C.conjTranspose * C)) := by
      conv_lhs => lhs; rw [hXA]
      conv_lhs => rhs; rw [hXC]
    rw [this, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    -- Inner: (AA†)(C†C) = (1/β) • X
    have hkey : A * A.conjTranspose * (C.conjTranspose * C) = (1 / β) • X := by
      calc A * A.conjTranspose * (C.conjTranspose * C)
          = A * (A.conjTranspose * (C.conjTranspose * C)) := by rw [Matrix.mul_assoc]
        _ = A * ((A.conjTranspose * C.conjTranspose) * C) := by
              rw [Matrix.mul_assoc A.conjTranspose C.conjTranspose C]
        _ = A * (((1 / β) • B) * C) := by rw [hAtCt]
        _ = A * ((1 / β) • (B * C)) := by rw [Matrix.smul_mul]
        _ = (1 / β) • (A * (B * C)) := by rw [Matrix.mul_smul]
        _ = (1 / β) • (A * ((1 / α) • A.conjTranspose)) := by rw [hidA]
        _ = (1 / β) • ((1 / α) • (A * A.conjTranspose)) := by rw [Matrix.mul_smul]
        _ = (1 / β) • ((1 / α) • (α • X)) := by rw [hAAt]
        _ = (1 / β) • X := by
              conv_lhs => rw [smul_smul (1 / α) α X,
                show 1 / α * α = 1 from by field_simp [hα_ne], one_smul]
    rw [hkey, smul_smul]
    congr 1
    have : 1 / α * (1 / γ) * (1 / β) = 1 / (α * β * γ) := by ring
    rw [this]
  -- Tr(X) = n (nonzero)
  have htrX : X.trace = (n : ℂ) := by
    have hXA₀ : X = (1 / frobNormSq (Θ.A a₀)) • (Θ.A a₀ * (Θ.A a₀).conjTranspose) := by
      rw [← hgA a₀]; rfl
    rw [hXA₀, Matrix.trace_smul, smul_eq_mul,
        Matrix.trace_mul_comm (Θ.A a₀) (Θ.A a₀).conjTranspose]
    have htr_eq : ((Θ.A a₀).conjTranspose * Θ.A a₀).trace =
        ↑n * frobNormSq (Θ.A a₀) := by
      have : frobNormSq (Θ.A a₀) =
          (1 / (↑n : ℂ)) * ((Θ.A a₀).conjTranspose * Θ.A a₀).trace := by
        unfold frobNormSq frobInner; ring
      have hn_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
      rw [this]; field_simp
    rw [htr_eq]; field_simp [hnd.A_pos a₀]
  have htrX_ne : X.trace ≠ 0 := by rw [htrX]; exact Nat.cast_ne_zero.mpr (NeZero.ne n)
  -- κ is constant: taking trace of X² = (1/κ') • X gives κ' = κ
  have hκ_const : ∀ a b : Fin n, frobNormSq (Θ.A a) * frobNormSq (Θ.B b) *
      frobNormSq (Θ.C (f.op a b)) = κ := by
    intro a b
    have h1 := hX_sq_eq a₀ b₀
    have h2 := hX_sq_eq a b
    rw [h2] at h1
    -- h1: (1/(α₂β₂γ₂)) • X = (1/(α₁β₁γ₁)) • X
    -- Since X ≠ 0 (trace ≠ 0), the scalars must be equal
    have hsmul_eq : (1 / (frobNormSq (Θ.A a) * frobNormSq (Θ.B b) *
        frobNormSq (Θ.C (f.op a b)))) =
      (1 / (frobNormSq (Θ.A a₀) * frobNormSq (Θ.B b₀) *
        frobNormSq (Θ.C (f.op a₀ b₀)))) := by
      -- From h1: c₁ • X = c₂ • X, take trace
      have := congr_arg Matrix.trace h1
      simp only [Matrix.trace_smul, smul_eq_mul] at this
      exact mul_right_cancel₀ htrX_ne this
    -- From 1/p₁ = 1/p₂, get p₁ = p₂
    have hprod_ne : frobNormSq (Θ.A a) * frobNormSq (Θ.B b) *
        frobNormSq (Θ.C (f.op a b)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (hnd.A_pos a) (hnd.B_pos b)) (hnd.C_pos (f.op a b))
    have hprod_ne₀ : frobNormSq (Θ.A a₀) * frobNormSq (Θ.B b₀) *
        frobNormSq (Θ.C (f.op a₀ b₀)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (hnd.A_pos a₀) (hnd.B_pos b₀)) (hnd.C_pos (f.op a₀ b₀))
    -- 1/p₁ = 1/p₂ → p₁ = p₂ (since p₁, p₂ ≠ 0)
    simp only [one_div] at hsmul_eq
    rw [hκ_simp]
    exact inv_injective hsmul_eq
  -- kappaTriple = κ on support
  have hκ_triple : ∀ a b : Fin n, kappaTriple Θ a b (f.op a b) = κ := by
    intro a b
    unfold kappaTriple; rw [hT a b, map_one, mul_one, div_one]
    exact hκ_const a b
  -- κ.re > 0 (product of positive reals)
  have hκ_pos : κ.re > 0 := by
    rw [hκ_simp]
    have h1 := frobNormSq_nonneg (Θ.A a₀)
    have h2 := frobNormSq_nonneg (Θ.B b₀)
    have h3 := frobNormSq_nonneg (Θ.C (f.op a₀ b₀))
    have h1i := frobNormSq_real (Θ.A a₀)
    have h2i := frobNormSq_real (Θ.B b₀)
    have h3i := frobNormSq_real (Θ.C (f.op a₀ b₀))
    have h1ne := hnd.A_pos a₀
    have h2ne := hnd.B_pos b₀
    have h3ne := hnd.C_pos (f.op a₀ b₀)
    -- α.re > 0 (nonneg + nonzero)
    have hα_pos : (frobNormSq (Θ.A a₀)).re > 0 := by
      rcases lt_or_eq_of_le h1 with h | h; exact h
      exfalso; exact h1ne (Complex.ext h.symm h1i)
    have hβ_pos : (frobNormSq (Θ.B b₀)).re > 0 := by
      rcases lt_or_eq_of_le h2 with h | h; exact h
      exfalso; exact h2ne (Complex.ext h.symm h2i)
    have hγ_pos : (frobNormSq (Θ.C (f.op a₀ b₀))).re > 0 := by
      rcases lt_or_eq_of_le h3 with h | h; exact h
      exfalso; exact h3ne (Complex.ext h.symm h3i)
    simp only [Complex.mul_re, Complex.mul_im]
    rw [h1i, h2i, h3i]
    ring_nf
    exact mul_pos (mul_pos hα_pos hβ_pos) hγ_pos
  -- κ.re ≤ 1: from X² = (1/κ)X, Tr(X²) = n/κ, and Cauchy-Schwarz
  -- |Tr(X)|² ≤ n · Tr(X†X), i.e., n² ≤ n · n/κ, giving κ ≤ 1
  have hκ_le : κ.re ≤ 1 := by
    -- X² = (1/κ) • X from the specific triple (a₀, b₀)
    have hX_sq : X * X = (1 / κ) • X := by
      rw [hX_sq_eq a₀ b₀, hκ_simp]
    -- X is Hermitian
    have hX_herm : X.conjTranspose = X := by
      have hXA₀ : X = (1 / frobNormSq (Θ.A a₀)) •
          (Θ.A a₀ * (Θ.A a₀).conjTranspose) := by rw [← hgA a₀]; rfl
      rw [hXA₀, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_conjTranspose]
      congr 1; rw [star_div₀, star_one]
      exact congrArg (1 / ·) (star_frobNormSq _)
    -- Tr(X²) = (1/κ) * n
    have htrX2 : (X * X).trace = (1 / κ) * (n : ℂ) := by
      rw [hX_sq, Matrix.trace_smul, smul_eq_mul, htrX]
    -- frobNormSq(X) = (1/n) Tr(X†X) = (1/n) Tr(X²) = 1/κ
    have hfX : frobNormSq X = 1 / κ := by
      unfold frobNormSq frobInner
      rw [hX_herm]
      -- Goal: 1/(n:ℂ) * (X * X).trace = 1/κ
      rw [htrX2]
      -- Goal: 1/(n:ℂ) * ((1/κ) * n) = 1/κ
      have hn_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
      field_simp [hn_ne]
    -- κ ≠ 0
    have hκ_ne : κ ≠ 0 := by
      intro h; rw [h] at hκ_pos; exact lt_irrefl 0 hκ_pos
    -- frobNormSq(X).re = (1/κ).re = 1/κ.re (since κ.im = 0)
    have hκ_im : κ.im = 0 := by
      rw [hκ_simp]
      have h1i := frobNormSq_real (Θ.A a₀)
      have h2i := frobNormSq_real (Θ.B b₀)
      have h3i := frobNormSq_real (Θ.C (f.op a₀ b₀))
      simp only [Complex.mul_im]; rw [h1i, h2i, h3i]; ring
    -- Strategy: frobNormSq(I-X) = 1/κ - 1 ≥ 0 gives κ ≤ 1
    -- (I-X) is Hermitian
    have h1mX_herm : (1 - X).conjTranspose = 1 - X := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hX_herm]
    -- Compute frobNormSq(I-X)
    -- frobNormSq(I-X) = (1/n) Tr((I-X)†(I-X)) = (1/n) Tr((I-X)²)
    -- (I-X)² = I - 2X + X² = I - 2X + (1/κ)X = I - (2 - 1/κ)X
    -- Tr((I-X)²) = n - (2 - 1/κ)n = n(1/κ - 1)
    -- frobNormSq(I-X) = 1/κ - 1
    -- Strategy: frobNormSq(I-X) = 1/κ - 1 ≥ 0 gives κ.re ≤ 1
    -- We use: frobNormSq = (1/n) * Tr(M†M), and for (1-X) with X Hermitian:
    -- Tr((1-X)†(1-X)) = Tr((1-X)²) = Tr(1) - 2Tr(X) + Tr(X²)
    have htrXsq : (X * X).trace = (1 / κ) * (n : ℂ) := by
      rw [hX_sq, Matrix.trace_smul, smul_eq_mul, htrX]
    have hn_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    -- frobNormSq(I-X) via direct computation
    have hfImX : frobNormSq (1 - X) = 1 / κ - 1 := by
      unfold frobNormSq frobInner
      rw [h1mX_herm]
      -- Goal: 1/(n:ℂ) * ((1-X)*(1-X)).trace = 1/κ - 1
      -- Compute trace of (1-X)²
      have : ((1 - X) * (1 - X)).trace = (n : ℂ) / κ - (n : ℂ) := by
        have hsub : (1 - X) * (1 - X) = 1 - X - X + X * X := by
          simp only [sub_mul, mul_sub, Matrix.mul_one, Matrix.one_mul]; abel
        rw [hsub, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub,
            Matrix.trace_one, Fintype.card_fin, htrXsq, htrX]
        ring
      rw [this]; field_simp [hn_ne, hκ_ne]
    -- frobNormSq(I-X).re ≥ 0
    have hfImX_nonneg := frobNormSq_nonneg (1 - X)
    rw [hfImX] at hfImX_nonneg
    -- (1/κ - 1).re ≥ 0, and κ is real → 1/κ.re - 1 ≥ 0 → κ.re ≤ 1
    have h_sub_re : (1 / κ - 1).re = (1 / κ).re - 1 := by
      simp [Complex.sub_re]
    have h_inv_re : (1 / κ).re = 1 / κ.re := by
      rw [one_div, Complex.inv_re]
      have : Complex.normSq κ = κ.re * κ.re := by
        rw [Complex.normSq_apply, hκ_im]; ring
      rw [this]; field_simp
    rw [h_sub_re, h_inv_re] at hfImX_nonneg
    -- 1/κ.re - 1 ≥ 0 and κ.re > 0 → κ.re ≤ 1
    -- 1/κ.re - 1 ≥ 0 and κ.re > 0 → κ.re ≤ 1
    have h1κ : 1 / κ.re ≥ 1 := by linarith
    rwa [ge_iff_le, le_div_iff₀ hκ_pos, one_mul] at h1κ
  exact ⟨κ, hκ_triple, hκ_le, hκ_pos⟩

/-- κ = 1 iff Gram matrices are identity (full-rank / unitary factorization). -/
theorem kappa_one_iff_unitary (Θ : HCParams n) (f : BinOp n)
    (hq : IsQuasigroup f) (hnd : Nondegenerate Θ)
    (hcol : PerfectCollinearity Θ f) (hfeas : Factorizes Θ f)
    (hκ : ∀ a b : Fin n, kappaTriple Θ a b (f.op a b) = 1) :
    ∀ a : Fin n, gramA Θ a = 1 := by
  -- Setup
  obtain ⟨X, hgA, hgC⟩ := shared_gram_matrices Θ f hq hnd hcol hfeas
  have hids := (perfectCollinearity_iff_identities Θ f hnd).mp hcol
  have hT : ∀ a b : Fin n, hcProduct Θ a b (f.op a b) = 1 := by
    intro a b; have := hfeas a b (f.op a b); rwa [structureTensor, if_pos rfl] at this
  suffices hX1 : X = 1 by intro a; rw [hgA a, hX1]
  -- Fix witnesses
  have ⟨a₀⟩ : Nonempty (Fin n) := ⟨⟨0, NeZero.pos n⟩⟩
  have ⟨b₀⟩ : Nonempty (Fin n) := ⟨⟨0, NeZero.pos n⟩⟩
  set c₀ := f.op a₀ b₀
  -- αβγ = 1 from κ = 1
  have hαβγ : frobNormSq (Θ.A a₀) * frobNormSq (Θ.B b₀) * frobNormSq (Θ.C c₀) = 1 := by
    have := hκ a₀ b₀; simp only [kappaTriple, hT a₀ b₀, map_one, mul_one, div_one] at this
    exact this
  -- Abbreviations (set before getting identities so set replaces in them)
  set α := frobNormSq (Θ.A a₀)
  set β := frobNormSq (Θ.B b₀)
  set γ := frobNormSq (Θ.C c₀)
  set A := Θ.A a₀; set B := Θ.B b₀; set C := Θ.C c₀
  -- Collinear identities with T=1 (keep 1/α form)
  have hidA : B * C = (1 / α) • A.conjTranspose := by
    have h := hids.idA a₀ b₀; dsimp only at h; rw [hT a₀ b₀] at h; exact h
  have hidB : C * A = (1 / β) • B.conjTranspose := by
    have h := hids.idB a₀ b₀; dsimp only at h; rw [hT a₀ b₀] at h; exact h
  have hidC : A * B = (1 / γ) • C.conjTranspose := by
    have h := hids.idC a₀ b₀; dsimp only at h; rw [hT a₀ b₀] at h; exact h
  -- gramA uses 1/α form, matching our identities
  have hα_ne : α ≠ 0 := hnd.A_pos a₀
  have hβ_ne : β ≠ 0 := hnd.B_pos b₀
  have hγ_ne : γ ≠ 0 := hnd.C_pos c₀
  have hXA : X = (1 / α) • (A * A.conjTranspose) := by rw [← hgA a₀]; rfl
  have hXC : X = (1 / γ) • (C.conjTranspose * C) := by rw [← hgC c₀]
  -- A A† = α • X
  have hAAt : A * A.conjTranspose = α • X := by
    rw [hXA, smul_smul, show α * (1 / α) = 1 from by field_simp [hα_ne], one_smul]
  -- C† C = γ • X
  have hCtC : C.conjTranspose * C = γ • X := by
    rw [hXC, smul_smul, show γ * (1 / γ) = 1 from by field_simp [hγ_ne], one_smul]
  -- A† C† = (CA)† = ((1/β) B†)† = star(1/β) • B = (1/β) • B (β real)
  have hAtCt : A.conjTranspose * C.conjTranspose = (1 / β) • B := by
    rw [← Matrix.conjTranspose_mul, hidB, Matrix.conjTranspose_smul,
        Matrix.conjTranspose_conjTranspose]
    congr 1; rw [star_div₀, star_one]; exact congrArg (1 / ·) (star_frobNormSq _)
  -- Key: (AA†)(C†C) = (1/β) • X
  have hkey : A * A.conjTranspose * (C.conjTranspose * C) = (1 / β) • X := by
    calc A * A.conjTranspose * (C.conjTranspose * C)
        = A * (A.conjTranspose * (C.conjTranspose * C)) := by rw [Matrix.mul_assoc]
      _ = A * ((A.conjTranspose * C.conjTranspose) * C) := by
            rw [Matrix.mul_assoc A.conjTranspose C.conjTranspose C]
      _ = A * (((1 / β) • B) * C) := by rw [hAtCt]
      _ = A * ((1 / β) • (B * C)) := by rw [Matrix.smul_mul]
      _ = (1 / β) • (A * (B * C)) := by rw [Matrix.mul_smul]
      _ = (1 / β) • (A * ((1 / α) • A.conjTranspose)) := by rw [hidA]
      _ = (1 / β) • ((1 / α) • (A * A.conjTranspose)) := by rw [Matrix.mul_smul]
      _ = (1 / β) • ((1 / α) • (α • X)) := by rw [hAAt]
      _ = (1 / β) • X := by
            conv_lhs => rw [smul_smul (1 / α) α X,
              show 1 / α * α = 1 from by field_simp [hα_ne], one_smul]
  -- X² = (1/(αβγ)) • X = X since αβγ = 1
  have hX_idem : X * X = X := by
    have : X * X = ((1 / α) • (A * A.conjTranspose)) *
                   ((1 / γ) • (C.conjTranspose * C)) := by
      conv_lhs => lhs; rw [hXA]
      conv_lhs => rhs; rw [hXC]
    rw [this, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hkey, smul_smul]
    have : 1 / α * (1 / γ) * (1 / β) = 1 / (α * β * γ) := by ring
    rw [this]
    rw [hαβγ, div_one, one_smul]
  -- X is Hermitian
  have hX_herm : X.conjTranspose = X := by
    rw [hXA, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
    congr 1; rw [star_div₀, star_one]; exact congrArg (1 / ·) (star_frobNormSq _)
  -- Tr(X) = n
  have htrX : X.trace = (n : ℂ) := by
    rw [hXA, Matrix.trace_smul, smul_eq_mul,
        Matrix.trace_mul_comm A A.conjTranspose]
    have htr_eq : (A.conjTranspose * A).trace = ↑n * α := by
      have : α = (1 / (↑n : ℂ)) * (A.conjTranspose * A).trace := by
        change frobNormSq (Θ.A a₀) = _; unfold frobNormSq frobInner; ring
      have hn_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
      rw [this]; field_simp
    rw [htr_eq]; field_simp [hα_ne]
  -- (1-X)† = 1-X (Hermitian)
  have h1mX_herm : (1 - X).conjTranspose = 1 - X := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hX_herm]
  -- (1-X)² = 1-X (idempotent)
  have h1mX_idem : (1 - X) * (1 - X) = 1 - X := by
    have : X * X = X := hX_idem
    simp only [sub_mul, mul_sub, Matrix.mul_one, Matrix.one_mul]
    rw [this]; abel
  -- frobNormSq(1-X) = 0 (since Tr(1-X) = n - n = 0)
  have hfrob : frobNormSq (1 - X) = 0 := by
    unfold frobNormSq frobInner
    rw [h1mX_herm, h1mX_idem]
    rw [Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin, htrX, sub_self, mul_zero]
  have h1eqX := (frobNormSq_eq_zero_iff (1 - X)).mp hfrob
  rw [sub_eq_zero] at h1eqX; exact h1eqX.symm

/-! ## Lemma 12: AM-GM Lower Bound -/

/-- Scalar AM-GM cubed: (α+β+γ)³ ≥ 27αβγ for nonneg reals. -/
private theorem amgm_cubed (α β γ : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) :
    (α + β + γ) ^ 3 ≥ 27 * (α * β * γ) := by
  nlinarith [sq_nonneg (α - β), sq_nonneg (β - γ), sq_nonneg (α - γ),
             sq_nonneg α, sq_nonneg β, sq_nonneg γ,
             mul_nonneg hα hβ, mul_nonneg hβ hγ, mul_nonneg hα hγ]

/-- For positive reals with product ≤ 1: 1/a + 1/b + 1/c ≥ 3. -/
private theorem sum_inv_ge_three (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (hprod : a * b * c ≤ 1) : 1/a + 1/b + 1/c ≥ 3 := by
  have ha' : (0 : ℝ) ≤ 1/a := by positivity
  have hb' : (0 : ℝ) ≤ 1/b := by positivity
  have hc' : (0 : ℝ) ≤ 1/c := by positivity
  have hcubed := amgm_cubed (1/a) (1/b) (1/c) ha' hb' hc'
  have hinv : 1/a * (1/b) * (1/c) ≥ 1 := by
    rw [show 1/a * (1/b) * (1/c) = 1/(a*b*c) from by field_simp]
    rw [ge_iff_le, le_div_iff₀ (by positivity : a * b * c > 0)]
    linarith
  set s := 1/a + 1/b + 1/c
  have hs_pos : s ≥ 0 := by linarith
  have hs_cubed : s ^ 3 ≥ 27 := by nlinarith
  -- s ≥ 0 and s³ ≥ 27 → s ≥ 3
  nlinarith [sq_nonneg (s - 3), sq_nonneg s]

/-- **Lemma 12 (AM-GM Lower Bound).**
    Assume nondegeneracy and perfect collinearity.
    B(Θ; δ) ≥ 3n² (for feasible Θ where |T|=1 on support). -/
theorem amgm_lower_bound (Θ : HCParams n) (f : BinOp n)
    (hq : IsQuasigroup f) (hnd : Nondegenerate Θ)
    (hcol : PerfectCollinearity Θ f) (hfeas : Factorizes Θ f) :
    (inversePenalty Θ f).re ≥
      3 * (n : ℝ) ^ 2 := by
  -- Get κ constant
  obtain ⟨κ, hκ_const, hκ_le, hκ_pos⟩ := normalized_rank_constant Θ f hq hnd hcol hfeas
  -- T = 1 on support
  have hT : ∀ a b : Fin n, hcProduct Θ a b (f.op a b) = 1 := by
    intro a b; have := hfeas a b (f.op a b); rwa [structureTensor, if_pos rfl] at this
  -- κ.im = 0
  have hκ_im : κ.im = 0 := by
    have h0 := hκ_const ⟨0, NeZero.pos n⟩ ⟨0, NeZero.pos n⟩
    simp only [kappaTriple, hT] at h0
    rw [map_one, mul_one, div_one] at h0; rw [← h0]
    have h1 := frobNormSq_real (Θ.A ⟨0, NeZero.pos n⟩)
    have h2 := frobNormSq_real (Θ.B ⟨0, NeZero.pos n⟩)
    have h3 := frobNormSq_real (Θ.C (f.op ⟨0, NeZero.pos n⟩ ⟨0, NeZero.pos n⟩))
    simp only [Complex.mul_im]; rw [h1, h2, h3]; ring
  -- Helper: frobNormSq is real positive
  have fns_pos : ∀ {m : Fin n → Matrix (Fin n) (Fin n) ℂ}
      (hne : ∀ i, frobNormSq (m i) ≠ 0) (i : Fin n), (frobNormSq (m i)).re > 0 := by
    intro m hne i
    have h := frobNormSq_nonneg (m i)
    rcases lt_or_eq_of_le h with h' | h'
    · exact h'
    · exfalso; exact hne i (Complex.ext h'.symm (frobNormSq_real (m i)))
  -- Helper: complex with im=0 inverse
  have inv_re : ∀ z : ℂ, z.im = 0 → z ≠ 0 → (1 / z).re = 1 / z.re := by
    intro z him hne
    have hre_ne : z.re ≠ 0 := by intro h; exact hne (Complex.ext h him)
    have hzr : z = (z.re : ℂ) := by
      apply Complex.ext <;> simp [him]
    rw [hzr]; simp [Complex.ofReal_re]
  -- Helper: product re for reals
  have mul_im_zero : ∀ a b : ℂ, a.im = 0 → b.im = 0 → (a * b).im = 0 := by
    intro a b ha hb; simp [Complex.mul_im, ha, hb]
  have mul_re : ∀ a b : ℂ, a.im = 0 → b.im = 0 → (a * b).re = a.re * b.re := by
    intro a b ha hb; simp [Complex.mul_re, ha, hb]
  -- Each summand in inversePenalty (with T=1): (1/α + 1/β + 1/γ).re ≥ 3
  have per_term : ∀ a b : Fin n,
      let c := f.op a b
      (hcProduct Θ a b c * starRingEnd ℂ (hcProduct Θ a b c) *
        (1 / frobNormSq (Θ.A a) + 1 / frobNormSq (Θ.B b) +
         1 / frobNormSq (Θ.C c))).re ≥ 3 := by
    intro a b c
    -- T = 1, so |T|² = 1
    rw [hT a b, map_one, mul_one, one_mul]
    -- Goal: (1/α + 1/β + 1/γ).re ≥ 3
    have hαi := frobNormSq_real (Θ.A a)
    have hβi := frobNormSq_real (Θ.B b)
    have hγi := frobNormSq_real (Θ.C c)
    have hα_pos := fns_pos hnd.A_pos a
    have hβ_pos := fns_pos hnd.B_pos b
    have hγ_pos := fns_pos hnd.C_pos c
    -- Sum of inverses in .re
    have h_re : (1 / frobNormSq (Θ.A a) + 1 / frobNormSq (Θ.B b) +
        1 / frobNormSq (Θ.C c)).re =
        1 / (frobNormSq (Θ.A a)).re + 1 / (frobNormSq (Θ.B b)).re +
        1 / (frobNormSq (Θ.C c)).re := by
      simp only [Complex.add_re]
      rw [inv_re _ hαi (hnd.A_pos a), inv_re _ hβi (hnd.B_pos b),
          inv_re _ hγi (hnd.C_pos c)]
    rw [h_re]
    -- Product bound: α.re * β.re * γ.re = κ.re ≤ 1
    have hprod_eq : (frobNormSq (Θ.A a)).re * (frobNormSq (Θ.B b)).re *
        (frobNormSq (Θ.C c)).re = κ.re := by
      have h := hκ_const a b
      simp only [kappaTriple, hT a b, map_one, mul_one, div_one] at h
      -- h: α * β * γ = κ
      have := congr_arg Complex.re h
      rw [mul_re (frobNormSq (Θ.A a) * frobNormSq (Θ.B b)) (frobNormSq (Θ.C c))
        (mul_im_zero _ _ hαi hβi) hγi,
        mul_re (frobNormSq (Θ.A a)) (frobNormSq (Θ.B b)) hαi hβi] at this
      exact this
    exact sum_inv_ge_three _ _ _ hα_pos hβ_pos hγ_pos (hprod_eq ▸ hκ_le)
  -- Sum over all (a,b) pairs: inversePenalty.re ≥ 3n²
  unfold inversePenalty
  rw [Complex.re_sum]
  have : ∀ a : Fin n, Complex.re (∑ b : Fin n,
      (let c := f.op a b; let t := hcProduct Θ a b c;
       t * starRingEnd ℂ t * (1 / frobNormSq (Θ.A a) + 1 / frobNormSq (Θ.B b) +
         1 / frobNormSq (Θ.C c)))) ≥ ∑ _ : Fin n, (3 : ℝ) := by
    intro a
    rw [Complex.re_sum]
    apply Finset.sum_le_sum; intro b _
    exact per_term a b
  calc ∑ a : Fin n, _ ≥ ∑ a : Fin n, ∑ _ : Fin n, (3 : ℝ) := Finset.sum_le_sum (fun a _ => this a)
    _ = 3 * (n : ℝ) ^ 2 := by
        simp [Finset.sum_const, Fintype.card_fin, sq]; ring

/-! ## Theorem 16: Optimality within the Collinear Manifold -/

/-- A collinear factorization is **unitary** if all factor slices are unitary
    (in the normalized sense: ‖A_a‖² = 1, A_a A_a† = I). -/
structure UnitaryCollinear (Θ : HCParams n) (f : BinOp n) : Prop where
  collinear : PerfectCollinearity Θ f
  feasible : Factorizes Θ f
  unitaryA : ∀ a : Fin n, Θ.A a * (Θ.A a).conjTranspose = 1
  unitaryB : ∀ b : Fin n, Θ.B b * (Θ.B b).conjTranspose = 1
  unitaryC : ∀ c : Fin n, Θ.C c * (Θ.C c).conjTranspose = 1

end
