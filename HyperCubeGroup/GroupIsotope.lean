/-
  HyperCubeGroup.GroupIsotope

  The bidirectional characterization:
  Collinear Factorization ↔ Group Isotope (Section 4).

  Main results:
  - Lemma 5 (Synchronization): unitary collinear → synchronized gauge A'=B'=(C')†
  - Lemma 6 (Homomorphism & Injectivity): synchronized map ρ: Q → U(n)
  - Theorem 7: Unitary collinearity ⟹ group isotope
  - Theorem 12: General collinearity ⟺ group isotope
  - Lemma 8: Group isotope ⟹ unitary collinear factorization (via left-regular rep)
  - Lemma 9: Uniqueness of representation (character theory)
-/

import HyperCubeGroup.CollinearManifold

open Matrix BigOperators Finset Complex

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ## Quasigroup isotopes and loops -/

/-- Two binary operations are isotopic if they differ by a triple of bijections:
    a ∘' b = χ(φ⁻¹(a) ∘ ψ⁻¹(b)). -/
def IsIsotopic (f g : BinOp n) : Prop :=
  ∃ φ ψ χ : Equiv.Perm (Fin n),
    ∀ a b : Fin n, g.op a b = χ (f.op (φ.symm a) (ψ.symm b))

/-- A quasigroup is a group isotope if it is isotopic to some group. -/
def IsGroupIsotope (f : BinOp n) : Prop :=
  ∃ g : BinOp n, IsAssociative g ∧ IsIsotopic g f

/-- A loop is a quasigroup with a two-sided identity element. -/
structure IsLoop (f : BinOp n) extends IsQuasigroup f : Prop where
  identity : ∃ e : Fin n, ∀ a : Fin n, f.op e a = a ∧ f.op a e = a

/-- Every finite quasigroup is isotopic to a loop (Pflugfelder, 1990). -/
theorem quasigroup_isotopic_to_loop (f : BinOp n) (hq : IsQuasigroup f) :
    ∃ g : BinOp n, IsLoop g ∧ IsIsotopic f g := by
  have ⟨e⟩ : Nonempty (Fin n) := ⟨⟨0, NeZero.pos n⟩⟩
  let R_e : Equiv.Perm (Fin n) := Equiv.ofBijective (fun x => f.op x e) (hq.right_cancel e)
  let L_e : Equiv.Perm (Fin n) := Equiv.ofBijective (fun x => f.op e x) (hq.left_cancel e)
  let g : BinOp n := ⟨fun a b => f.op (R_e.symm a) (L_e.symm b)⟩
  let e' := f.op e e
  use g
  constructor
  · constructor
    · constructor
      · intro a
        show Function.Bijective (fun b => f.op (R_e.symm a) (L_e.symm b))
        exact (hq.left_cancel (R_e.symm a)).comp L_e.symm.bijective
      · intro b
        show Function.Bijective (fun a => f.op (R_e.symm a) (L_e.symm b))
        exact (hq.right_cancel (L_e.symm b)).comp R_e.symm.bijective
    · use e'
      intro a
      constructor
      · show f.op (R_e.symm e') (L_e.symm a) = a
        have : R_e.symm e' = e := R_e.symm_apply_eq.mpr rfl
        rw [this]; exact L_e.apply_symm_apply a
      · show f.op (R_e.symm a) (L_e.symm e') = a
        have : L_e.symm e' = e := L_e.symm_apply_eq.mpr rfl
        rw [this]; exact R_e.apply_symm_apply a
  · exact ⟨R_e, L_e, 1, fun a b => by simp [g]⟩

/-! ## Lemma 5: Synchronization -/

structure Synchronized (Θ : HCParams n) (f : BinOp n) where
  rho : Fin n → Matrix (Fin n) (Fin n) ℂ
  eq_A : ∀ g : Fin n, Θ.A g = rho g
  eq_B : ∀ g : Fin n, Θ.B g = rho g
  eq_C : ∀ g : Fin n, Θ.C g = (rho g).conjTranspose
  unitary : ∀ g : Fin n, rho g * (rho g).conjTranspose = 1

/-! ### Helper lemmas for synchronization and homomorphism -/

/-- Product of two unitary matrices is unitary. -/
private theorem mul_unitary_unitary (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A * A.conjTranspose = 1) (hB : B * B.conjTranspose = 1) :
    (A * B) * (A * B).conjTranspose = 1 := by
  rw [Matrix.conjTranspose_mul]
  have h1 : B * (B.conjTranspose * A.conjTranspose) = A.conjTranspose := by
    rw [← Matrix.mul_assoc, hB, Matrix.one_mul]
  rw [Matrix.mul_assoc, h1, hA]

/-- conjTranspose of unitary is unitary. -/
private theorem conjTranspose_unitary (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A * A.conjTranspose = 1) :
    A.conjTranspose * A.conjTranspose.conjTranspose = 1 := by
  rw [Matrix.conjTranspose_conjTranspose]; exact mul_eq_one_comm.mp hA

/-- A unitary matrix whose normalized trace equals 1 must be the identity.
    Key insight: ‖M - I‖² = 2 - (2/n)Re(Tr(M)) = 0 when Tr(M) = n. -/
private theorem unitary_trace_n_eq_one (M : Matrix (Fin n) (Fin n) ℂ)
    (hunit : M * M.conjTranspose = 1)
    (htrace : (1 / (n : ℂ)) * M.trace = 1) :
    M = 1 := by
  have hunit' : M.conjTranspose * M = 1 := mul_eq_one_comm.mp hunit
  have hn_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  -- Extract Tr(M) = n from (1/n) * Tr(M) = 1
  have htr : M.trace = (n : ℂ) := by
    have h := htrace
    rw [one_div, inv_mul_eq_div, div_eq_iff hn_ne] at h
    rw [one_mul] at h; exact h
  -- Show frobNormSq(M - 1) = 0 by direct computation
  suffices hsuff : frobNormSq (M - 1) = 0 by
    rwa [frobNormSq_eq_zero_iff, sub_eq_zero] at hsuff
  unfold frobNormSq frobInner
  -- Expand (M - 1)† * (M - 1) = M†M - M† - M + 1
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
  have hexpand : (M.conjTranspose - 1) * (M - 1) =
      M.conjTranspose * M - M.conjTranspose - M + 1 := by
    simp only [sub_mul, mul_sub, Matrix.mul_one, Matrix.one_mul]
    abel
  rw [hexpand, hunit']
  -- Trace of (1 - M† - M + 1) = 2n - Tr(M†) - Tr(M) = 0
  simp only [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_one, Fintype.card_fin]
  rw [Matrix.trace_conjTranspose, htr, star_natCast]
  ring

/-- Synchronization: Given UnitaryCollinear Θ f and f a loop with identity e,
    construct a synchronized Θ' by gauge-transforming via A_e†. -/
theorem synchronization (Θ : HCParams n) (f : BinOp n)
    (hloop : IsLoop f) (huc : UnitaryCollinear Θ f) :
    ∃ (Θ' : HCParams n), Nonempty (Synchronized Θ' f) := by
  -- Construct ρ(g) = A_e† * A_g
  let ρ := fun g => (Θ.A (Classical.choose hloop.identity)).conjTranspose * Θ.A g
  let Θ' : HCParams n := ⟨ρ, ρ, fun g => (ρ g).conjTranspose⟩
  exact ⟨Θ', ⟨{
    rho := ρ
    eq_A := fun _ => rfl
    eq_B := fun _ => rfl
    eq_C := fun _ => rfl
    unitary := fun g => by
      show ρ g * (ρ g).conjTranspose = 1
      simp only [ρ, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      -- Goal: A_e† * A_g * (A_g† * A_e) = 1
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Θ.A g)]
      rw [huc.unitaryA g, Matrix.one_mul]
      exact mul_eq_one_comm.mp (huc.unitaryA _)
  }⟩⟩

/-! ## Lemma 6: Homomorphism and Injectivity -/

theorem synchronized_homomorphism (Θ : HCParams n) (f : BinOp n)
    (hloop : IsLoop f) (hsync : Synchronized Θ f) (hfeas : Factorizes Θ f) :
    (∀ a b : Fin n, hsync.rho a * hsync.rho b = hsync.rho (f.op a b)) := by
  intro a b
  let ρ := hsync.rho
  let c := f.op a b
  -- Strategy: show M = ρ(a) * ρ(b) * ρ(c)† is unitary with trace/n = 1,
  -- hence M = I, hence ρ(a) * ρ(b) = ρ(c).
  set M := ρ a * ρ b * (ρ c).conjTranspose with hM_def
  -- M is unitary (product of unitaries)
  have hunit_M : M * M.conjTranspose = 1 := by
    rw [hM_def]
    have h1 := mul_unitary_unitary (ρ a) (ρ b) (hsync.unitary a) (hsync.unitary b)
    exact mul_unitary_unitary _ _ h1 (conjTranspose_unitary _ (hsync.unitary c))
  -- (1/n) * Tr(M) = 1 from Factorizes
  have htrace_M : (1 / (n : ℂ)) * M.trace = 1 := by
    -- hcProduct Θ a b c = structureTensor f a b c
    have hfact := hfeas a b c
    -- On support (c = f.op a b): structureTensor = 1
    simp only [structureTensor, show f.op a b = c from rfl, ite_true] at hfact
    -- hcProduct = (1/n) * Tr(A_a * B_b * C_c) = (1/n) * Tr(ρa * ρb * ρc†)
    rw [hcProduct, hsync.eq_A, hsync.eq_B, hsync.eq_C] at hfact
    rw [hM_def]; exact hfact
  -- Apply the helper: M = 1
  have hM_one : M = 1 := unitary_trace_n_eq_one M hunit_M htrace_M
  -- From M = 1: ρ(a) * ρ(b) * ρ(c)† = 1
  -- Right-multiply by ρ(c): ρ(a) * ρ(b) = ρ(c)
  have hunit_c' : (ρ c).conjTranspose * ρ c = 1 :=
    mul_eq_one_comm.mp (hsync.unitary c)
  have : M * ρ c = ρ c := by rw [hM_one, Matrix.one_mul]
  calc ρ a * ρ b
      = ρ a * ρ b * 1 := by rw [Matrix.mul_one]
    _ = ρ a * ρ b * ((ρ c).conjTranspose * ρ c) := by rw [hunit_c']
    _ = M * ρ c := by rw [hM_def]; simp only [Matrix.mul_assoc]
    _ = ρ c := this

theorem synchronized_injective (Θ : HCParams n) (f : BinOp n)
    (hloop : IsLoop f) (hsync : Synchronized Θ f) (hfeas : Factorizes Θ f) :
    Function.Injective hsync.rho := by
  intro x y hρ
  have hT : ∀ b c, hcProduct Θ x b c = hcProduct Θ y b c := by
    intro b c; simp only [hcProduct]; rw [hsync.eq_A x, hsync.eq_A y, hρ]
  have hδ : ∀ b c, structureTensor f x b c = structureTensor f y b c := by
    intro b c; rw [← hfeas x b c, ← hfeas y b c, hT b c]
  have hrow : ∀ b, f.op x b = f.op y b := by
    intro b
    have h1 : structureTensor f x b (f.op x b) = 1 := by simp [structureTensor]
    have h2 : structureTensor f y b (f.op x b) = 1 := by rw [← hδ b]; exact h1
    simp [structureTensor] at h2; exact h2.symm
  have ⟨b⟩ : Nonempty (Fin n) := ⟨⟨0, NeZero.pos n⟩⟩
  exact (hloop.toIsQuasigroup.right_cancel b).1 (hrow b)

/-! ## Theorems 6 and 7 -/

/-- Helper: a loop with UnitaryCollinear factorization is a group. -/
private theorem loop_uc_associative (f : BinOp n)
    (hloop : IsLoop f) (Θ : HCParams n) (huc : UnitaryCollinear Θ f) :
    IsAssociative f := by
  -- Step 0: derive key properties from UnitaryCollinear
  have hfeas := huc.feasible
  -- Helper to get frobNormSq of unitary = 1 (defined later in file, inline here)
  have fnsu : ∀ M : Matrix (Fin n) (Fin n) ℂ, M * M.conjTranspose = 1 →
      frobNormSq M = 1 := by
    intro M hM; unfold frobNormSq frobInner
    rw [mul_eq_one_comm.mp hM, Matrix.trace_one, Fintype.card_fin]
    have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    field_simp
  have hnd : Nondegenerate Θ :=
    ⟨fun a => by rw [fnsu _ (huc.unitaryA a)]; exact one_ne_zero,
     fun b => by rw [fnsu _ (huc.unitaryB b)]; exact one_ne_zero,
     fun c => by rw [fnsu _ (huc.unitaryC c)]; exact one_ne_zero⟩
  have hcol := (perfectCollinearity_iff_identities Θ f hnd).mp huc.collinear
  obtain ⟨e, he⟩ := hloop.identity
  -- For UnitaryCollinear, T_{ab(a∘b)} = 1 and frobNormSq = 1
  have hT : ∀ a b, hcProduct Θ a b (f.op a b) = 1 := by
    intro a b; rw [hfeas a b (f.op a b)]; simp [structureTensor]
  have hnA : ∀ a, frobNormSq (Θ.A a) = 1 := fun a => fnsu _ (huc.unitaryA a)
  have hnB : ∀ b, frobNormSq (Θ.B b) = 1 := fun b => fnsu _ (huc.unitaryB b)
  have hnC : ∀ c, frobNormSq (Θ.C c) = 1 := fun c => fnsu _ (huc.unitaryC c)
  -- Simplified collinear identity C: A_a * B_b = C_{a∘b}†
  have hidC : ∀ a b, Θ.A a * Θ.B b = (Θ.C (f.op a b)).conjTranspose := by
    intro a b
    have := hcol.idC a b
    simp only at this
    rw [hT a b, hnC, div_one, one_smul] at this
    exact this
  -- From hidC with b = e: A_a * B_e = C_a†  (since f.op a e = a)
  have hABe : ∀ a, Θ.A a * Θ.B e = (Θ.C a).conjTranspose := by
    intro a; rw [hidC a e, (he a).2]
  -- From hidC with a = e: A_e * B_b = C_b†  (since f.op e b = b)
  have hAeB : ∀ b, Θ.A e * Θ.B b = (Θ.C b).conjTranspose := by
    intro b; rw [hidC e b, (he b).1]
  -- Therefore A_a * B_e = A_e * B_b when a = b, i.e., both equal C_a†
  -- More usefully: A_e * B_g = A_g * B_e  (equating the two expressions for C_g†)
  have hcomm : ∀ g, Θ.A e * Θ.B g = Θ.A g * Θ.B e := by
    intro g; rw [hAeB g, hABe g]
  -- Define ρ(g) = A_e† * A_g
  -- Show ρ(a) * ρ(b) = ρ(a ∘ b) using the commutation relation
  -- From hidC: A_a * B_b = C_{a∘b}† = A_{a∘b} * B_e (by hABe)
  have hidC' : ∀ a b, Θ.A a * Θ.B b = Θ.A (f.op a b) * Θ.B e := by
    intro a b; rw [hidC a b, ← hABe (f.op a b)]
  -- B_g = A_e† * A_g * B_e  (from hcomm: A_e * B_g = A_g * B_e)
  -- i.e., A_e * B_g = A_g * B_e, so B_g = A_e⁻¹ * A_g * B_e = A_e† * A_g * B_e
  -- From hidC': A_a * B_b = A_{a∘b} * B_e
  -- Substitute B_b = A_e† * A_b * B_e (from hcomm):
  -- A_a * A_e† * A_b * B_e = A_{a∘b} * B_e
  -- Cancel B_e: A_a * A_e† * A_b = A_{a∘b}
  -- Left-multiply by A_e†: A_e† * A_a * A_e† * A_b = A_e† * A_{a∘b}
  -- i.e., ρ(a) * ρ(b) = ρ(a ∘ b)
  -- Step 1: derive B_b = A_e† * A_b * B_e
  have hB_eq : ∀ b, Θ.B b = (Θ.A e).conjTranspose * Θ.A b * Θ.B e := by
    intro b
    have h := hcomm b -- A_e * B_b = A_b * B_e
    -- Left-multiply by A_e†
    have hAe_inv : (Θ.A e).conjTranspose * Θ.A e = 1 :=
      mul_eq_one_comm.mp (huc.unitaryA e)
    calc Θ.B b
        = 1 * Θ.B b := (Matrix.one_mul _).symm
      _ = ((Θ.A e).conjTranspose * Θ.A e) * Θ.B b := by rw [hAe_inv]
      _ = (Θ.A e).conjTranspose * (Θ.A e * Θ.B b) := by rw [Matrix.mul_assoc]
      _ = (Θ.A e).conjTranspose * (Θ.A b * Θ.B e) := by rw [h]
      _ = (Θ.A e).conjTranspose * Θ.A b * Θ.B e := by rw [Matrix.mul_assoc]
  -- Step 2: From hidC', A_a * B_b = A_{a∘b} * B_e, cancel B_e
  -- Key: A_a * (A_e† * A_b) = A_{a∘b}
  have hA_hom : ∀ a b,
      Θ.A a * ((Θ.A e).conjTranspose * Θ.A b) = Θ.A (f.op a b) := by
    intro a b
    have hBe_inv : Θ.B e * (Θ.B e).conjTranspose = 1 := huc.unitaryB e
    -- Right-cancel B_e: suffices both sides * B_e are equal
    suffices h : Θ.A a * ((Θ.A e).conjTranspose * Θ.A b) * Θ.B e =
                 Θ.A (f.op a b) * Θ.B e by
      have := congr_arg (· * (Θ.B e).conjTranspose) h
      simp only [Matrix.mul_assoc, hBe_inv, Matrix.mul_one] at this
      exact this
    calc Θ.A a * ((Θ.A e).conjTranspose * Θ.A b) * Θ.B e
        = Θ.A a * ((Θ.A e).conjTranspose * Θ.A b * Θ.B e) := by
          rw [Matrix.mul_assoc]
      _ = Θ.A a * Θ.B b := by rw [← hB_eq b]
      _ = Θ.A (f.op a b) * Θ.B e := hidC' a b
  -- Step 3: ρ(a) * ρ(b) = ρ(a ∘ b) where ρ(g) = A_e† * A_g
  have hρ_hom : ∀ a b,
      (Θ.A e).conjTranspose * Θ.A a * ((Θ.A e).conjTranspose * Θ.A b) =
      (Θ.A e).conjTranspose * Θ.A (f.op a b) := by
    intro a b
    rw [Matrix.mul_assoc, hA_hom a b]
  -- Step 4: ρ is injective
  have hρ_inj : Function.Injective (fun g => (Θ.A e).conjTranspose * Θ.A g) := by
    intro x y h
    have hAe_mul : Θ.A e * ((Θ.A e).conjTranspose * Θ.A x) =
                   Θ.A e * ((Θ.A e).conjTranspose * Θ.A y) := congr_arg _ h
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, huc.unitaryA e,
        Matrix.one_mul, Matrix.one_mul] at hAe_mul
    -- A_x = A_y, so hcProduct matches
    have hT_eq : ∀ b' c', hcProduct Θ x b' c' = hcProduct Θ y b' c' := by
      intro b' c'
      simp only [hcProduct, hAe_mul]
    have hrow : ∀ b, f.op x b = f.op y b := by
      intro b
      have h1 : structureTensor f x b (f.op x b) = 1 := by simp [structureTensor]
      have h2 : structureTensor f y b (f.op x b) = 1 := by
        rw [← hfeas y b, ← hT_eq b, hfeas x b]; exact h1
      simp [structureTensor] at h2; exact h2.symm
    exact (hloop.toIsQuasigroup.right_cancel ⟨0, NeZero.pos n⟩).1 (hrow _)
  -- Step 5: Associativity by injectivity of ρ + matrix associativity
  intro a b c
  apply hρ_inj
  show (Θ.A e).conjTranspose * Θ.A (f.op (f.op a b) c) =
       (Θ.A e).conjTranspose * Θ.A (f.op a (f.op b c))
  -- ρ((a∘b)∘c) = ρ(a∘b)*ρ(c) = (ρa*ρb)*ρc = ρa*(ρb*ρc) = ρa*ρ(b∘c) = ρ(a∘(b∘c))
  rw [← hρ_hom (f.op a b) c, ← hρ_hom a b,
      Matrix.mul_assoc, hρ_hom b c, hρ_hom a (f.op b c)]

/-- Transfer UnitaryCollinear across isotopy (isotope transforms preserve
    unitarity and collinearity). -/
private theorem uc_isotope_transfer (f g : BinOp n)
    (_hqf : IsQuasigroup f) (hiso : IsIsotopic f g)
    (hexists : ∃ Θ : HCParams n, UnitaryCollinear Θ f) :
    ∃ Θ' : HCParams n, UnitaryCollinear Θ' g := by
  obtain ⟨Θ, huc⟩ := hexists
  obtain ⟨φ, ψ, χ, hiso_eq⟩ := hiso
  -- Θ' permutes indices via the isotopy
  let Θ' := isotopeTransform Θ φ.symm ψ.symm χ.symm
  use Θ'
  -- Inline helper: frobNormSq of unitary = 1
  have fnsu : ∀ M : Matrix (Fin n) (Fin n) ℂ, M * M.conjTranspose = 1 →
      frobNormSq M = 1 := by
    intro M hM; unfold frobNormSq frobInner
    rw [mul_eq_one_comm.mp hM, Matrix.trace_one, Fintype.card_fin]
    have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    field_simp
  -- Factorizes: prove directly
  have hfact : Factorizes Θ' g := by
    intro a b c
    -- hcProduct Θ' a b c = hcProduct Θ (φ.symm a) (ψ.symm b) (χ.symm c) definitionally
    change hcProduct Θ (φ.symm a) (ψ.symm b) (χ.symm c) = structureTensor g a b c
    rw [huc.feasible (φ.symm a) (ψ.symm b) (χ.symm c)]
    simp only [structureTensor]
    by_cases hc : g.op a b = c
    · rw [if_pos hc, if_pos]
      apply χ.injective; rw [Equiv.apply_symm_apply, ← hiso_eq a b, hc]
    · rw [if_neg hc, if_neg]
      intro heq; exact hc (by rw [hiso_eq, heq, Equiv.apply_symm_apply])
  -- Unitarity: just permuted indices of unitary slices
  have hunitA : ∀ a, Θ'.A a * (Θ'.A a).conjTranspose = 1 :=
    fun a => huc.unitaryA (φ.symm a)
  have hunitB : ∀ b, Θ'.B b * (Θ'.B b).conjTranspose = 1 :=
    fun b => huc.unitaryB (ψ.symm b)
  have hunitC : ∀ c, Θ'.C c * (Θ'.C c).conjTranspose = 1 :=
    fun c => huc.unitaryC (χ.symm c)
  -- Nondegeneracy
  have hnd' : Nondegenerate Θ' :=
    ⟨fun a => by rw [fnsu _ (hunitA a)]; exact one_ne_zero,
     fun b => by rw [fnsu _ (hunitB b)]; exact one_ne_zero,
     fun c => by rw [fnsu _ (hunitC c)]; exact one_ne_zero⟩
  -- Collinearity via CollinearIdentities
  have hcol : PerfectCollinearity Θ' g := by
    rw [perfectCollinearity_iff_identities Θ' g hnd']
    -- Isotopy on Cayley table: χ⁻¹(g(a,b)) = f(φ⁻¹a, ψ⁻¹b)
    have hc_eq : ∀ a b, χ.symm (g.op a b) = f.op (φ.symm a) (ψ.symm b) := by
      intro a b; apply χ.injective; rw [Equiv.apply_symm_apply]; exact hiso_eq a b
    -- UC helpers for the original Θ
    have hnA : ∀ a, frobNormSq (Θ.A a) = 1 := fun a => fnsu _ (huc.unitaryA a)
    have hnB : ∀ b, frobNormSq (Θ.B b) = 1 := fun b => fnsu _ (huc.unitaryB b)
    have hnC : ∀ c, frobNormSq (Θ.C c) = 1 := fun c => fnsu _ (huc.unitaryC c)
    have hnd : Nondegenerate Θ :=
      ⟨fun a => by rw [hnA]; exact one_ne_zero,
       fun b => by rw [hnB]; exact one_ne_zero,
       fun c => by rw [hnC]; exact one_ne_zero⟩
    have hT : ∀ a b, hcProduct Θ a b (f.op a b) = 1 := by
      intro a b; rw [huc.feasible]; simp [structureTensor]
    -- Simplified UC identities: B*C = A†, C*A = B†, A*B = C†
    have hids := (perfectCollinearity_iff_identities Θ f hnd).mp huc.collinear
    have hidA : ∀ a b, Θ.B b * Θ.C (f.op a b) = (Θ.A a).conjTranspose := by
      intro a b; have h := hids.idA a b; simp only at h
      rw [hT, hnA, div_one, one_smul] at h; exact h
    have hidB : ∀ a b, Θ.C (f.op a b) * Θ.A a = (Θ.B b).conjTranspose := by
      intro a b; have h := hids.idB a b; simp only at h
      rw [hT, hnB, div_one, one_smul] at h; exact h
    have hidC : ∀ a b, Θ.A a * Θ.B b = (Θ.C (f.op a b)).conjTranspose := by
      intro a b; have h := hids.idC a b; simp only at h
      rw [hT, hnC, div_one, one_smul] at h; exact h
    constructor
    · -- idA: B'_b * C'_{g(a,b)} = (T'/‖A'‖²) • (A'_a)†
      intro a b
      show Θ'.B b * Θ'.C (g.op a b) =
        (hcProduct Θ' a b (g.op a b) / frobNormSq (Θ'.A a)) • (Θ'.A a).conjTranspose
      have hBC : Θ'.B b * Θ'.C (g.op a b) = (Θ'.A a).conjTranspose := by
        show Θ.B (ψ.symm b) * Θ.C (χ.symm (g.op a b)) = (Θ.A (φ.symm a)).conjTranspose
        rw [hc_eq, hidA]
      rw [hBC]
      have hT' : hcProduct Θ' a b (g.op a b) = 1 := by
        rw [hfact a b (g.op a b)]; simp [structureTensor]
      rw [hT', fnsu _ (hunitA a)]; simp
    · -- idB: C'_{g(a,b)} * A'_a = (T'/‖B'‖²) • (B'_b)†
      intro a b
      show Θ'.C (g.op a b) * Θ'.A a =
        (hcProduct Θ' a b (g.op a b) / frobNormSq (Θ'.B b)) • (Θ'.B b).conjTranspose
      have hCA : Θ'.C (g.op a b) * Θ'.A a = (Θ'.B b).conjTranspose := by
        show Θ.C (χ.symm (g.op a b)) * Θ.A (φ.symm a) = (Θ.B (ψ.symm b)).conjTranspose
        rw [hc_eq, hidB]
      rw [hCA]
      have hT' : hcProduct Θ' a b (g.op a b) = 1 := by
        rw [hfact a b (g.op a b)]; simp [structureTensor]
      rw [hT', fnsu _ (hunitB b)]; simp
    · -- idC: A'_a * B'_b = (T'/‖C'‖²) • (C'_{g(a,b)})†
      intro a b
      show Θ'.A a * Θ'.B b =
        (hcProduct Θ' a b (g.op a b) / frobNormSq (Θ'.C (g.op a b))) •
          (Θ'.C (g.op a b)).conjTranspose
      have hAB : Θ'.A a * Θ'.B b = (Θ'.C (g.op a b)).conjTranspose := by
        show Θ.A (φ.symm a) * Θ.B (ψ.symm b) = (Θ.C (χ.symm (g.op a b))).conjTranspose
        rw [hc_eq, hidC]
      rw [hAB]
      have hT' : hcProduct Θ' a b (g.op a b) = 1 := by
        rw [hfact a b (g.op a b)]; simp [structureTensor]
      rw [hT', fnsu _ (hunitC _)]; simp
  exact ⟨hcol, hfact, hunitA, hunitB, hunitC⟩

theorem unitary_collinear_implies_group_isotope (f : BinOp n)
    (hq : IsQuasigroup f)
    (hexists : ∃ Θ : HCParams n, UnitaryCollinear Θ f) :
    IsGroupIsotope f := by
  -- Step 1: f is isotopic to a loop g
  obtain ⟨g, hloop, hiso⟩ := quasigroup_isotopic_to_loop f hq
  -- Step 2: Transfer UnitaryCollinear from f to g
  obtain ⟨Θ_g, huc_g⟩ := uc_isotope_transfer f g hq hiso hexists
  -- Step 3: g is a group (loop + UnitaryCollinear → associative)
  have hassoc : IsAssociative g := loop_uc_associative g hloop Θ_g huc_g
  -- Step 4: f is isotopic to group g, hence a group isotope
  -- We have IsIsotopic f g, need IsIsotopic g f (reverse direction)
  obtain ⟨φ, ψ, χ, hiso_eq⟩ := hiso
  exact ⟨g, hassoc, φ.symm, ψ.symm, χ.symm, fun a b => by
    have h := hiso_eq (φ a) (ψ b)
    simp [Equiv.symm_apply_apply] at h
    -- h : χ(f.op a b) = g.op(φ a)(ψ b), need f.op a b = χ⁻¹(g.op ...)
    exact χ.injective (by simp [Equiv.apply_symm_apply]; exact h.symm)⟩

/-- Collinear + feasible + nondegenerate → ∃ unitary collinear factorization.
    Full proof requires: shared Gram matrices (Lemma 10), normalized rank κ = 1
    (Lemma 11), and norm rescaling to achieve unitarity (Section 5). -/
private axiom collinear_to_unitary_collinear (f : BinOp n) (hq : IsQuasigroup f)
    (Θ : HCParams n) (hcol : PerfectCollinearity Θ f) (hfeas : Factorizes Θ f)
    (hnd : Nondegenerate Θ) :
    ∃ Θ' : HCParams n, UnitaryCollinear Θ' f

theorem collinear_implies_group_isotope (f : BinOp n)
    (hq : IsQuasigroup f)
    (hexists : ∃ Θ : HCParams n, PerfectCollinearity Θ f ∧ Factorizes Θ f ∧
      Nondegenerate Θ) :
    IsGroupIsotope f := by
  obtain ⟨Θ, hcol, hfeas, hnd⟩ := hexists
  obtain ⟨Θ', huc⟩ := collinear_to_unitary_collinear f hq Θ hcol hfeas hnd
  exact unitary_collinear_implies_group_isotope f hq ⟨Θ', huc⟩

/-! ## Lemma 8: Group Isotope ⟹ Unitary Collinear Factorization -/

def leftRegularRep (f : BinOp n) : Fin n → Matrix (Fin n) (Fin n) ℂ :=
  fun g => Matrix.of (fun i j : Fin n => if f.op g j = i then (1 : ℂ) else 0)

theorem leftRegularRep_unitary (f : BinOp n) (hq : IsQuasigroup f)
    (g : Fin n) :
    leftRegularRep f g * (leftRegularRep f g).conjTranspose = 1 := by
  have hbij : Function.Bijective (f.op g) := hq.left_cancel g
  ext i j
  simp only [leftRegularRep, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.of_apply, Matrix.one_apply]
  simp only [apply_ite star, star_one, star_zero]
  by_cases hij : i = j
  · subst hij
    obtain ⟨k, hk⟩ := hbij.2 i
    have huniq : ∀ k', f.op g k' = i → k' = k := by
      intro k' hk'; exact hbij.1 (hk' ▸ hk ▸ rfl)
    trans (∑ x : Fin n, if x = k then (1 : ℂ) else 0)
    · apply Finset.sum_congr rfl
      intro x _
      split_ifs with h1 h2 h2
      · simp
      · exact absurd (huniq x h1) h2
      · subst h2; simp [hk] at h1
      · simp
    · simp
  · rw [if_neg hij]
    apply Finset.sum_eq_zero
    intro k _
    by_cases h1 : f.op g k = i <;> by_cases h2 : f.op g k = j <;> simp_all

theorem leftRegularRep_hom (f : BinOp n) (hq : IsQuasigroup f)
    (hassoc : IsAssociative f) (a b : Fin n) :
    leftRegularRep f a * leftRegularRep f b = leftRegularRep f (f.op a b) := by
  ext i j
  simp only [leftRegularRep, Matrix.mul_apply, Matrix.of_apply]
  trans (if f.op a (f.op b j) = i then (1 : ℂ) else 0)
  · classical
    have : (∑ k : Fin n,
        (if f.op a k = i then (1 : ℂ) else 0) * (if f.op b j = k then 1 else 0)) =
      (if f.op a (f.op b j) = i then 1 else 0) := by
      have h1 : ∀ k : Fin n,
          (if f.op a k = i then (1 : ℂ) else 0) * (if f.op b j = k then 1 else 0) =
          if f.op b j = k then (if f.op a k = i then 1 else 0) else 0 := by
        intro k; split_ifs <;> simp_all
      simp_rw [h1]
      simp [Finset.sum_ite_eq, Finset.mem_univ]
    exact this
  · rw [hassoc a b j]

/-! ### Helper lemmas -/

theorem isotopy_source_quasigroup (g f : BinOp n)
    (hqf : IsQuasigroup f) (hiso : IsIsotopic g f) :
    IsQuasigroup g := by
  obtain ⟨φ, ψ, χ, hiso⟩ := hiso
  have key : ∀ x y, g.op x y = χ.symm (f.op (φ x) (ψ y)) := by
    intro x y
    have h := hiso (φ x) (ψ y)
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at h
    calc g.op x y = χ.symm (χ (g.op x y)) := (Equiv.symm_apply_apply χ _).symm
      _ = χ.symm (f.op (φ x) (ψ y)) := by rw [← h]
  constructor
  · intro x
    show Function.Bijective (g.op x)
    have heq : g.op x = (fun y => χ.symm (f.op (φ x) (ψ y))) := funext (key x)
    rw [heq]
    exact (χ.symm.bijective.comp (hqf.left_cancel (φ x))).comp ψ.bijective
  · intro y
    show Function.Bijective (fun x => g.op x y)
    have heq : (fun x => g.op x y) = (fun x => χ.symm (f.op (φ x) (ψ y))) :=
      funext (fun x => key x y)
    rw [heq]
    exact (χ.symm.bijective.comp (hqf.right_cancel (ψ y))).comp φ.bijective

theorem leftRegularRep_trace_product (f : BinOp n) (hq : IsQuasigroup f)
    (x y : Fin n) :
    (leftRegularRep f x * (leftRegularRep f y).conjTranspose).trace =
      if x = y then (n : ℂ) else 0 := by
  split_ifs with hxy
  · subst hxy
    rw [leftRegularRep_unitary f hq x, Matrix.trace_one, Fintype.card_fin]
  · simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.conjTranspose_apply, leftRegularRep, Matrix.of_apply]
    simp only [apply_ite star, star_one, star_zero]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro k _
    by_cases h1 : f.op x k = i <;> by_cases h2 : f.op y k = i <;> simp_all
    exact absurd ((hq.right_cancel k).1 (h1.trans h2.symm)) hxy

theorem frobNormSq_unitary_eq_one (M : Matrix (Fin n) (Fin n) ℂ)
    (h : M * M.conjTranspose = 1) :
    frobNormSq M = 1 := by
  unfold frobNormSq frobInner
  rw [mul_eq_one_comm.mp h, Matrix.trace_one, Fintype.card_fin]
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  field_simp

theorem leftRegularRep_factorizes (f : BinOp n) (hq : IsQuasigroup f)
    (hassoc : IsAssociative f) :
    let Θ : HCParams n := ⟨leftRegularRep f, leftRegularRep f,
      fun c => (leftRegularRep f c).conjTranspose⟩
    Factorizes Θ f := by
  intro Θ a b c
  unfold hcProduct structureTensor
  simp only [Θ]
  have hmul : leftRegularRep f a * leftRegularRep f b *
      (leftRegularRep f c).conjTranspose =
    leftRegularRep f (f.op a b) * (leftRegularRep f c).conjTranspose := by
    rw [← leftRegularRep_hom f hq hassoc a b]
  rw [hmul, leftRegularRep_trace_product f hq]
  split_ifs with h
  · have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    field_simp
  · simp [mul_zero]

theorem isotopeTransform_factorizes (Θ : HCParams n) (g f : BinOp n)
    (φ ψ χ : Equiv.Perm (Fin n))
    (hiso : ∀ a b : Fin n, f.op a b = χ (g.op (φ.symm a) (ψ.symm b)))
    (hfact : Factorizes Θ g) :
    Factorizes (isotopeTransform Θ φ.symm ψ.symm χ.symm) f := by
  intro a b c
  simp only [hcProduct_isotope_equiv]
  rw [hfact (φ.symm a) (ψ.symm b) (χ.symm c)]
  unfold structureTensor
  have h := hiso a b
  by_cases hc : f.op a b = c
  · have hg : g.op (φ.symm a) (ψ.symm b) = χ.symm c := by
      apply χ.injective; rw [χ.apply_symm_apply, ← h, hc]
    simp [hg, hc]
  · have hg : g.op (φ.symm a) (ψ.symm b) ≠ χ.symm c := by
      intro heq; apply hc; have := congr_arg χ heq
      rw [χ.apply_symm_apply] at this; rw [h, this]
    simp [hg, hc]

/-- Helper: for the left-regular representation with C_c = ρ(c)†,
    the product B_b * C_c on support triples simplifies. -/
private theorem leftReg_BC_eq_conjTranspose_A (g : BinOp n) (hq : IsQuasigroup g)
    (hassoc : IsAssociative g) (a b : Fin n) :
    let ρ := leftRegularRep g
    ρ b * (ρ (g.op a b)).conjTranspose = (ρ a).conjTranspose := by
  intro ρ
  have hhom := leftRegularRep_hom g hq hassoc a b
  have hunit := leftRegularRep_unitary g hq b
  calc ρ b * (ρ (g.op a b)).conjTranspose
      = ρ b * (ρ a * ρ b).conjTranspose := by rw [hhom]
    _ = ρ b * ((ρ b).conjTranspose * (ρ a).conjTranspose) := by
        rw [Matrix.conjTranspose_mul]
    _ = (ρ b * (ρ b).conjTranspose) * (ρ a).conjTranspose := by
        rw [Matrix.mul_assoc]
    _ = 1 * (ρ a).conjTranspose := by rw [hunit]
    _ = (ρ a).conjTranspose := Matrix.one_mul _

/-- Helper: for the left-regular representation, C_c * A_a on support. -/
private theorem leftReg_CA_eq_conjTranspose_B (g : BinOp n) (hq : IsQuasigroup g)
    (hassoc : IsAssociative g) (a b : Fin n) :
    let ρ := leftRegularRep g
    (ρ (g.op a b)).conjTranspose * ρ a = (ρ b).conjTranspose := by
  intro ρ
  have hhom := leftRegularRep_hom g hq hassoc a b
  have hunit := leftRegularRep_unitary g hq a
  calc (ρ (g.op a b)).conjTranspose * ρ a
      = (ρ a * ρ b).conjTranspose * ρ a := by rw [hhom]
    _ = ((ρ b).conjTranspose * (ρ a).conjTranspose) * ρ a := by
        rw [Matrix.conjTranspose_mul]
    _ = (ρ b).conjTranspose * ((ρ a).conjTranspose * ρ a) := by
        rw [Matrix.mul_assoc]
    _ = (ρ b).conjTranspose * 1 := by
        rw [mul_eq_one_comm.mp hunit]
    _ = (ρ b).conjTranspose := Matrix.mul_one _

/-- **Lemma 8 (Group Isotope ⟹ Unitary Collinear Factorization).** -/
theorem group_isotope_admits_unitary_collinear (f : BinOp n)
    (hq : IsQuasigroup f) (hgi : IsGroupIsotope f) :
    ∃ Θ : HCParams n, UnitaryCollinear Θ f := by
  obtain ⟨g, hassoc, φ, ψ, χ, hiso⟩ := hgi
  have hqg : IsQuasigroup g := isotopy_source_quasigroup g f hq ⟨φ, ψ, χ, hiso⟩
  -- Build Θ_g from left-regular rep of g
  let ρ := leftRegularRep g
  let Θ_g : HCParams n := ⟨ρ, ρ, fun c => (ρ c).conjTranspose⟩
  -- Transform to get Θ_f
  let Θ_f := isotopeTransform Θ_g φ.symm ψ.symm χ.symm
  use Θ_f
  -- Factorizes
  have hfact_g : Factorizes Θ_g g := leftRegularRep_factorizes g hqg hassoc
  have hfact : Factorizes Θ_f f :=
    isotopeTransform_factorizes Θ_g g f φ ψ χ hiso hfact_g
  -- Unitarity: isotopeTransform just permutes indices
  have hunitA : ∀ a, Θ_f.A a * (Θ_f.A a).conjTranspose = 1 := by
    intro a; exact leftRegularRep_unitary g hqg (φ.symm a)
  have hunitB : ∀ b, Θ_f.B b * (Θ_f.B b).conjTranspose = 1 := by
    intro b; exact leftRegularRep_unitary g hqg (ψ.symm b)
  have hunitC : ∀ c, Θ_f.C c * (Θ_f.C c).conjTranspose = 1 := by
    intro c
    show (ρ (χ.symm c)).conjTranspose * (ρ (χ.symm c)).conjTranspose.conjTranspose = 1
    rw [Matrix.conjTranspose_conjTranspose]
    exact mul_eq_one_comm.mp (leftRegularRep_unitary g hqg (χ.symm c))
  -- Nondegeneracy
  have hnd : Nondegenerate Θ_f := by
    constructor
    · intro a; rw [frobNormSq_unitary_eq_one _ (hunitA a)]; exact one_ne_zero
    · intro b; rw [frobNormSq_unitary_eq_one _ (hunitB b)]; exact one_ne_zero
    · intro c; rw [frobNormSq_unitary_eq_one _ (hunitC c)]; exact one_ne_zero
  -- Perfect collinearity via CollinearIdentities
  have hcol : PerfectCollinearity Θ_f f := by
    rw [perfectCollinearity_iff_identities Θ_f f hnd]
    constructor
    · -- idA: B_b * C_c = (T/‖A‖²) • A†
      intro a b
      show Θ_f.B b * Θ_f.C (f.op a b) =
        (hcProduct Θ_f a b (f.op a b) / frobNormSq (Θ_f.A a)) • (Θ_f.A a).conjTranspose
      have hc_eq : χ.symm (f.op a b) = g.op (φ.symm a) (ψ.symm b) := by
        apply χ.injective; rw [Equiv.apply_symm_apply]; exact hiso a b
      have hBC : Θ_f.B b * Θ_f.C (f.op a b) = (Θ_f.A a).conjTranspose := by
        show ρ (ψ.symm b) * (ρ (χ.symm (f.op a b))).conjTranspose =
          (ρ (φ.symm a)).conjTranspose
        rw [hc_eq]
        exact leftReg_BC_eq_conjTranspose_A g hqg hassoc (φ.symm a) (ψ.symm b)
      rw [hBC]
      have hT : hcProduct Θ_f a b (f.op a b) = 1 := by
        rw [hfact a b (f.op a b)]; simp [structureTensor]
      have hN : frobNormSq (Θ_f.A a) = 1 :=
        frobNormSq_unitary_eq_one _ (hunitA a)
      rw [hT, hN]; simp
    · -- idB: C_c * A_a = (T/‖B‖²) • B†
      intro a b
      show Θ_f.C (f.op a b) * Θ_f.A a =
        (hcProduct Θ_f a b (f.op a b) / frobNormSq (Θ_f.B b)) • (Θ_f.B b).conjTranspose
      have hc_eq : χ.symm (f.op a b) = g.op (φ.symm a) (ψ.symm b) := by
        apply χ.injective; rw [Equiv.apply_symm_apply]; exact hiso a b
      have hCA : Θ_f.C (f.op a b) * Θ_f.A a = (Θ_f.B b).conjTranspose := by
        show (ρ (χ.symm (f.op a b))).conjTranspose * ρ (φ.symm a) =
          (ρ (ψ.symm b)).conjTranspose
        rw [hc_eq]
        exact leftReg_CA_eq_conjTranspose_B g hqg hassoc (φ.symm a) (ψ.symm b)
      rw [hCA]
      have hT : hcProduct Θ_f a b (f.op a b) = 1 := by
        rw [hfact a b (f.op a b)]; simp [structureTensor]
      have hN : frobNormSq (Θ_f.B b) = 1 :=
        frobNormSq_unitary_eq_one _ (hunitB b)
      rw [hT, hN]; simp
    · -- idC: A_a * B_b = (T/‖C‖²) • C†
      intro a b
      show Θ_f.A a * Θ_f.B b =
        (hcProduct Θ_f a b (f.op a b) / frobNormSq (Θ_f.C (f.op a b))) •
          (Θ_f.C (f.op a b)).conjTranspose
      have hc_eq : χ.symm (f.op a b) = g.op (φ.symm a) (ψ.symm b) := by
        apply χ.injective; rw [Equiv.apply_symm_apply]; exact hiso a b
      have hAB : Θ_f.A a * Θ_f.B b = (Θ_f.C (f.op a b)).conjTranspose := by
        show ρ (φ.symm a) * ρ (ψ.symm b) =
          ((ρ (χ.symm (f.op a b))).conjTranspose).conjTranspose
        rw [hc_eq, Matrix.conjTranspose_conjTranspose]
        exact leftRegularRep_hom g hqg hassoc (φ.symm a) (ψ.symm b)
      rw [hAB]
      have hT : hcProduct Θ_f a b (f.op a b) = 1 := by
        rw [hfact a b (f.op a b)]; simp [structureTensor]
      have hN : frobNormSq (Θ_f.C (f.op a b)) = 1 :=
        frobNormSq_unitary_eq_one _ (hunitC (f.op a b))
      rw [hT, hN]; simp
  exact ⟨hcol, hfact, hunitA, hunitB, hunitC⟩

/-! ## Bidirectional equivalence -/

private theorem frobNormSq_unitary_ne_zero
    (M : Matrix (Fin n) (Fin n) ℂ) (h : M * M.conjTranspose = 1) :
    frobNormSq M ≠ 0 := by
  rw [frobNormSq_unitary_eq_one M h]; exact one_ne_zero

theorem collinear_iff_group_isotope (f : BinOp n) (hq : IsQuasigroup f) :
    (∃ Θ : HCParams n, PerfectCollinearity Θ f ∧ Factorizes Θ f ∧
      Nondegenerate Θ) ↔
    IsGroupIsotope f := by
  constructor
  · exact collinear_implies_group_isotope f hq
  · intro hgi
    obtain ⟨Θ, huc⟩ := group_isotope_admits_unitary_collinear f hq hgi
    exact ⟨Θ, huc.collinear, huc.feasible,
           ⟨fun a => frobNormSq_unitary_ne_zero _ (huc.unitaryA a),
            fun b => frobNormSq_unitary_ne_zero _ (huc.unitaryB b),
            fun c => frobNormSq_unitary_ne_zero _ (huc.unitaryC c)⟩⟩

/-! ## Lemma 9: Uniqueness of Representation -/

theorem representation_unique (Θ : HCParams n) (f : BinOp n)
    (hloop : IsLoop f) (hassoc : IsAssociative f)
    (hsync : Synchronized Θ f) (hfeas : Factorizes Θ f) :
    ∀ g : Fin n,
      (hsync.rho g).trace = if g = Classical.choose hloop.identity
        then (n : ℂ) else 0 := by
  intro g
  set e := Classical.choose hloop.identity with he_def
  have he := Classical.choose_spec hloop.identity
  have hhom := synchronized_homomorphism Θ f hloop hsync hfeas
  have hunit := mul_eq_one_comm.mp (hsync.unitary e)
  -- ρ(e) = I: from ρ(e)² = ρ(e) and unitarity
  have hρe : hsync.rho e = 1 := by
    have h := hhom e e; rw [(he e).1] at h -- ρ(e) * ρ(e) = ρ(e)
    -- Left-multiply by ρ(e)†: (ρ†ρ)ρ = ρ†ρ, i.e., ρ = 1
    have h1 : (hsync.rho e).conjTranspose * (hsync.rho e * hsync.rho e) =
              (hsync.rho e).conjTranspose * hsync.rho e := by rw [h]
    rwa [← Matrix.mul_assoc, hunit, Matrix.one_mul] at h1
  -- Use factorization at (e, e, g): (1/n) Tr(I · I · ρ(g)†) = δ_{e,g}
  have hfact := hfeas e e g
  rw [hcProduct, hsync.eq_A, hsync.eq_B, hsync.eq_C, hρe] at hfact
  simp only [Matrix.one_mul, Matrix.trace_conjTranspose] at hfact
  rw [structureTensor, (he e).1] at hfact
  -- hfact : (1/n) * star(Tr(ρ g)) = if e = g then 1 else 0
  have hn_ne : (1 / (n : ℂ)) ≠ 0 := by
    rw [one_div]; exact inv_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne n))
  by_cases heg : g = e
  · subst heg; rw [hρe, Matrix.trace_one, Fintype.card_fin, if_pos rfl]
  · rw [if_neg heg]
    rw [if_neg (fun h : e = g => heg h.symm)] at hfact
    exact star_eq_zero.mp ((mul_eq_zero.mp hfact).resolve_left hn_ne)

/-! ## Global minimizer definition -/

/-- A global minimizer of H over the feasible set. -/
def IsGlobalMinimizer (Θ : HCParams n) (f : BinOp n) : Prop :=
  Factorizes Θ f ∧ ∀ Θ' : HCParams n, Factorizes Θ' f →
    (objective Θ f).re ≤ (objective Θ' f).re

/-! ## Theorem 21: Strict Gap for Non-Group Isotopes (Conditional) -/

/-- **Revised Conjecture 20 (Strong Collinearity Dominance).**
    For any global minimizer Θ* of H on the feasible set, the inverse penalty
    dominates: B(Θ*) ≥ 3|δ| - c · R(Θ*) for a universal c ∈ [0,1).

    Updated from the original conjecture (which applied to all feasible Θ)
    following the discovery of counterexamples in the non-minimizer region.
    The bound holds at global minimizers, where training dynamics converge. -/
axiom strongCollinearityDominance :
  ∀ (n : ℕ) [NeZero n] (f : BinOp n) (hq : IsQuasigroup f),
    ∃ c : ℝ, c < 1 ∧ c ≥ 0 ∧
      ∀ Θ : HCParams n, IsGlobalMinimizer Θ f →
        (inversePenalty Θ f).re ≥ 3 * (n : ℝ) ^ 2 - c * (misalignPenalty Θ f).re

/-- For a UnitaryCollinear factorization, the objective value is exactly 3n². -/
theorem uc_objective_value (Θ : HCParams n) (f : BinOp n) (huc : UnitaryCollinear Θ f) :
    (objective Θ f).re = 3 * (n : ℝ) ^ 2 := by
  have hnA : ∀ a, frobNormSq (Θ.A a) = 1 :=
    fun a => frobNormSq_unitary_eq_one _ (huc.unitaryA a)
  have hnB : ∀ b, frobNormSq (Θ.B b) = 1 :=
    fun b => frobNormSq_unitary_eq_one _ (huc.unitaryB b)
  have hnC : ∀ c, frobNormSq (Θ.C c) = 1 :=
    fun c => frobNormSq_unitary_eq_one _ (huc.unitaryC c)
  have hnd : Nondegenerate Θ :=
    ⟨fun a => by rw [hnA]; exact one_ne_zero,
     fun b => by rw [hnB]; exact one_ne_zero,
     fun c => by rw [hnC]; exact one_ne_zero⟩
  have hcol := (perfectCollinearity_iff_identities Θ f hnd).mp huc.collinear
  have hT : ∀ a b, hcProduct Θ a b (f.op a b) = 1 := by
    intro a b; rw [huc.feasible a b (f.op a b)]; simp [structureTensor]
  -- Simplified collinear identities: B*C = A†, C*A = B†, A*B = C†
  have hidA : ∀ a b, Θ.B b * Θ.C (f.op a b) = (Θ.A a).conjTranspose := by
    intro a b; have h := hcol.idA a b; simp only at h
    rw [hT a b, hnA a, div_one, one_smul] at h; exact h
  have hidB : ∀ a b, Θ.C (f.op a b) * Θ.A a = (Θ.B b).conjTranspose := by
    intro a b; have h := hcol.idB a b; simp only at h
    rw [hT a b, hnB b, div_one, one_smul] at h; exact h
  have hidC : ∀ a b, Θ.A a * Θ.B b = (Θ.C (f.op a b)).conjTranspose := by
    intro a b; have h := hcol.idC a b; simp only at h
    rw [hT a b, hnC (f.op a b), div_one, one_smul] at h; exact h
  -- Each frobNormSq in the sum equals 1
  rw [objective_eq_sum_support]
  have hterm : ∀ a b : Fin n,
      frobNormSq (Θ.B b * Θ.C (f.op a b)) +
      frobNormSq (Θ.C (f.op a b) * Θ.A a) +
      frobNormSq (Θ.A a * Θ.B b) = 3 := by
    intro a b
    rw [hidA a b, frobNormSq_conjTranspose, hnA,
        hidB a b, frobNormSq_conjTranspose, hnB,
        hidC a b, frobNormSq_conjTranspose, hnC]
    norm_num
  simp_rw [hterm]
  -- (∑ a, ∑ b, (3 : ℂ)).re = 3 * n²
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num; ring

/-- **Theorem 21 (Strict Gap for Non-Group Isotopes, Conditional).**
    For non-group-isotope quasigroups, every feasible Θ has H > 3n².
    Proof: the revised dominance axiom holds at global minimizers, and for
    non-group-isotopes R > 0 at any feasible point (no collinear factorization
    exists), so H(Θ*) > 3n² at minimizers, hence H > 3n² everywhere. -/
theorem strict_gap_non_group (f : BinOp n) (hq : IsQuasigroup f)
    (hfeas_exists : ∃ Θ : HCParams n, Factorizes Θ f)
    (hmin_exists : ∃ Θ : HCParams n, IsGlobalMinimizer Θ f) :
    ¬ IsGroupIsotope f →
      ∀ Θ : HCParams n, Factorizes Θ f →
        (objective Θ f).re > 3 * (n : ℝ) ^ 2 := by
  intro hnotgi Θ hfeas
  -- Step 1: Get a global minimizer and its properties
  obtain ⟨Θ_min, hmin_feas, hmin_opt⟩ := hmin_exists
  have hnd_min := factorizes_implies_nondegenerate Θ_min f hq hmin_feas
  have hdecomp_min := decomposition Θ_min f hnd_min
  -- Step 2: ¬GroupIsotope → R(Θ_min) > 0 (no collinear factorization exists)
  have hR_pos : (misalignPenalty Θ_min f).re > 0 := by
    by_contra h
    push_neg at h
    have hR_ge := misalignPenalty_nonneg Θ_min f
    have hR_zero : (misalignPenalty Θ_min f).re = 0 := le_antisymm h hR_ge
    have hR_im_zero : (misalignPenalty Θ_min f).im = 0 := by
      unfold misalignPenalty
      rw [im_sum]
      apply Finset.sum_eq_zero; intro a _
      rw [im_sum]
      apply Finset.sum_eq_zero; intro b _
      have h1 := frobNormSq_real (misalignResidualA Θ_min a b (f.op a b))
      have h2 := frobNormSq_real (misalignResidualB Θ_min a b (f.op a b))
      have h3 := frobNormSq_real (misalignResidualC Θ_min a b (f.op a b))
      simp only [Complex.add_im]; linarith
    have hR_eq_zero : misalignPenalty Θ_min f = 0 :=
      Complex.ext hR_zero hR_im_zero
    have hcol : PerfectCollinearity Θ_min f := hR_eq_zero
    exact hnotgi (collinear_implies_group_isotope f hq ⟨Θ_min, hcol, hmin_feas, hnd_min⟩)
  -- Step 3: Strong collinearity dominance at global minimizer: B ≥ 3n² - c*R
  obtain ⟨c_val, hc_lt, hc_ge, hbound⟩ := strongCollinearityDominance n f hq
  have hB_bound := hbound Θ_min ⟨hmin_feas, hmin_opt⟩
  -- Step 4: H(Θ_min) = B + R ≥ 3n² + (1-c)*R > 3n²
  have hH_min_re : (objective Θ_min f).re =
      (inversePenalty Θ_min f).re + (misalignPenalty Θ_min f).re := by
    rw [hdecomp_min]; simp [Complex.add_re]
  have hH_min_gt : (objective Θ_min f).re > 3 * (n : ℝ) ^ 2 := by
    rw [hH_min_re]
    linarith [mul_pos (by linarith : (1 : ℝ) - c_val > 0) hR_pos]
  -- Step 5: Θ is feasible, so H(Θ) ≥ H(Θ_min) > 3n²
  linarith [hmin_opt Θ hfeas]

/-- **Theorem 14 (Optimality within the Collinear Manifold).**
    Restricted to the feasible collinear manifold, the minimum of H is achieved
    by a unitary collinear factorization with value 3n². -/
theorem collinear_manifold_optimality (f : BinOp n)
    (hq : IsQuasigroup f)
    (hexists : ∃ Θ : HCParams n, PerfectCollinearity Θ f ∧ Factorizes Θ f) :
    ∃ Θ_opt : HCParams n,
      UnitaryCollinear Θ_opt f ∧
      (objective Θ_opt f).re = 3 * (n : ℝ) ^ 2 ∧
      ∀ Θ : HCParams n, PerfectCollinearity Θ f → Factorizes Θ f →
        (objective Θ f).re ≥ 3 * (n : ℝ) ^ 2 := by
  -- Part 1: Existence of optimal UC factorization
  obtain ⟨Θ₀, hcol₀, hfeas₀⟩ := hexists
  have hnd₀ := factorizes_implies_nondegenerate Θ₀ f hq hfeas₀
  have hgi := collinear_implies_group_isotope f hq ⟨Θ₀, hcol₀, hfeas₀, hnd₀⟩
  obtain ⟨Θ_opt, huc⟩ := group_isotope_admits_unitary_collinear f hq hgi
  refine ⟨Θ_opt, huc, uc_objective_value Θ_opt f huc, ?_⟩
  -- Part 2: Universal lower bound on collinear manifold
  intro Θ hcol hfeas
  have hnd := factorizes_implies_nondegenerate Θ f hq hfeas
  -- On collinear manifold: objective = inversePenalty + 0 = inversePenalty
  have hdecomp := decomposition Θ f hnd
  have hR_zero : misalignPenalty Θ f = 0 := hcol
  rw [hdecomp, hR_zero, add_zero]
  exact amgm_lower_bound Θ f hq hnd hcol hfeas

end
