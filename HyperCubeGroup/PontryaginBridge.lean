/-
  HyperCubeGroup.PontryaginBridge

  Bridge from `IsAbelianGroup f` (a `BinOp n` carrying associative,
  commutative, identity-and-cancellation structure) to Mathlib's
  `AddCommGroup (Fin n)` and the `AddChar (Fin n) ℂ` machinery.

  This file:
    * Constructs an `AddCommGroup` instance on `Fin n` from
      `IsAbelianGroup f` via the quasigroup cancellation laws (which
      provide inverses through surjectivity).
    * Provides a `letI`-style helper so downstream code can pattern-match
      `IsAbelianGroup f` and recover the full Mathlib group-theoretic
      API on `Fin n`.

  ## Status

  Step 1 (AddCommGroup construction): mechanised here.
  Step 2 (use Mathlib's AddChar): free, no work needed.
  Step 3 (lift AddChar to Character f): mechanised here via
    `characterOfHom` and `addCharToCharacter`.
  Step 4 (orthogonality and completeness for CharacterBasis):
    mechanised here as `characterBasis`, using Mathlib's
    `AddChar.expect_eq_ite` (orthogonality) and
    `AddChar.sum_apply_eq_ite` (completeness via doubleDualEmb).
  -/

import HyperCubeGroup.Abelian
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

open Matrix BigOperators Complex

noncomputable section

variable {n : ℕ} [NeZero n]

namespace IsAbelianGroup

variable {f : BinOp n} (hab : IsAbelianGroup f)

/-- The identity element of an abelian-group binary operation. -/
def identityElt : Fin n := hab.identity.choose

theorem identityElt_left (a : Fin n) : f.op (hab.identityElt) a = a :=
  (hab.identity.choose_spec a).1

theorem identityElt_right (a : Fin n) : f.op a (hab.identityElt) = a :=
  (hab.identity.choose_spec a).2

/-- The (unique) inverse of `a`, defined via surjectivity of `f.op a`
    on the identity element. -/
def inv (a : Fin n) : Fin n :=
  ((hab.toIsQuasigroup.left_cancel a).surjective hab.identityElt).choose

/-- `a · inv a = e` (the right-inverse property). -/
theorem op_inv (a : Fin n) : f.op a (hab.inv a) = hab.identityElt :=
  ((hab.toIsQuasigroup.left_cancel a).surjective hab.identityElt).choose_spec

/-- `inv a · a = e` (the left-inverse property; follows from
    commutativity). -/
theorem inv_op (a : Fin n) : f.op (hab.inv a) a = hab.identityElt := by
  rw [hab.comm]; exact hab.op_inv a

/-- The constructed `AddCommGroup` instance on `Fin n` from
    `IsAbelianGroup f`. Uses Mathlib's `AddGroup.ofLeftAxioms` (with
    associativity, left identity, left inverse), then adds commutativity. -/
@[reducible] def toAddCommGroup : AddCommGroup (Fin n) :=
  letI : Add (Fin n) := ⟨f.op⟩
  letI : Zero (Fin n) := ⟨hab.identityElt⟩
  letI : Neg (Fin n) := ⟨hab.inv⟩
  letI : AddGroup (Fin n) :=
    AddGroup.ofLeftAxioms hab.assoc hab.identityElt_left hab.inv_op
  { (inferInstance : AddGroup (Fin n)) with
    add_comm := hab.comm }

/-! ## Wrapper type to escape the `Add (Fin n)` instance conflict -/

/-- `HCFin f hab` is `Fin n` carrying the abelian-group structure
    induced by `hab`, and *only* that abelian-group structure (not the
    standard mod-`n` `Add` instance on `Fin n`). This wrapper avoids
    the typeclass synthesis conflict described in the file-level
    note. -/
@[ext] structure HCFin {f : BinOp n} (_hab : IsAbelianGroup f) where
  /-- The underlying `Fin n` element. -/
  toFin : Fin n

namespace HCFin

variable {f : BinOp n} (hab : IsAbelianGroup f)

instance : DecidableEq (HCFin hab) := fun a b =>
  decidable_of_iff (a.toFin = b.toFin) ⟨HCFin.ext, fun h => by rw [h]⟩

/-- The underlying-`Fin n`-equiv. -/
def equivFin : HCFin hab ≃ Fin n where
  toFun := HCFin.toFin
  invFun := HCFin.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype (HCFin hab) := Fintype.ofEquiv (Fin n) (equivFin hab).symm

@[simp] theorem card_eq : Fintype.card (HCFin hab) = n := by
  rw [Fintype.card_congr (equivFin hab), Fintype.card_fin]

instance : Add (HCFin hab) := ⟨fun a b => ⟨f.op a.toFin b.toFin⟩⟩
instance : Zero (HCFin hab) := ⟨⟨hab.identityElt⟩⟩
instance : Neg (HCFin hab) := ⟨fun a => ⟨hab.inv a.toFin⟩⟩

/-- The abelian group structure on `HCFin hab`, lifted from `hab`. -/
instance : AddCommGroup (HCFin hab) :=
  letI : AddGroup (HCFin hab) :=
    AddGroup.ofLeftAxioms
      (fun a b c => by
        apply HCFin.ext
        show f.op (f.op a.toFin b.toFin) c.toFin = f.op a.toFin (f.op b.toFin c.toFin)
        exact hab.assoc a.toFin b.toFin c.toFin)
      (fun a => by
        apply HCFin.ext
        show f.op (hab.identityElt) a.toFin = a.toFin
        exact hab.identityElt_left a.toFin)
      (fun a => by
        apply HCFin.ext
        show f.op (hab.inv a.toFin) a.toFin = hab.identityElt
        exact hab.inv_op a.toFin)
  { (inferInstance : AddGroup (HCFin hab)) with
    add_comm := fun a b => by
      apply HCFin.ext
      show f.op a.toFin b.toFin = f.op b.toFin a.toFin
      exact hab.comm a.toFin b.toFin }

/-- For `ψ : AddChar (HCFin hab) ℂ` and `card_pos : 0 < n`, each
    `ψ a` has unit modulus (it is an `n`-th root of unity). -/
theorem addChar_normSq_one (ψ : AddChar (HCFin hab) ℂ) (a : HCFin hab) :
    Complex.normSq (ψ a) = 1 := by
  have hcard_pos : 0 < Fintype.card (HCFin hab) := by
    rw [card_eq]; exact Nat.pos_of_ne_zero (NeZero.ne n)
  -- (ψ a)^card = ψ (card • a) = ψ 0 = 1.
  have hpow : (ψ a) ^ (Fintype.card (HCFin hab)) = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero]
    exact ψ.map_zero_eq_one'
  -- normSq is multiplicative: |ψ a|^card = 1.
  have hnormSq_pow : Complex.normSq (ψ a) ^ Fintype.card (HCFin hab) = 1 := by
    rw [← map_pow, hpow, Complex.normSq_one]
  -- |ψ a| ≥ 0 with |ψ a|^card = 1 ⇒ |ψ a| = 1.
  have hnn : 0 ≤ Complex.normSq (ψ a) := Complex.normSq_nonneg _
  rcases lt_trichotomy (Complex.normSq (ψ a)) 1 with h | h | h
  · exfalso
    have : Complex.normSq (ψ a) ^ Fintype.card (HCFin hab) < 1 := by
      apply pow_lt_one₀ hnn h
      exact ne_of_gt hcard_pos
    linarith
  · exact h
  · exfalso
    have : 1 < Complex.normSq (ψ a) ^ Fintype.card (HCFin hab) :=
      one_lt_pow₀ h (ne_of_gt hcard_pos)
    linarith

end HCFin

/-! ## Step 3 partial: lift a hom-pair to `Character f` -/

/-- Construct a `Character f` from a function `val : Fin n → ℂ` with
    the homomorphism property `val (f.op a b) = val a * val b` and
    a unit-modulus condition. -/
def characterOfHom {f : BinOp n} (_hab : IsAbelianGroup f)
    (val : Fin n → ℂ)
    (hom : ∀ a b : Fin n, val (f.op a b) = val a * val b)
    (unit : ∀ a : Fin n, Complex.normSq (val a) = 1) :
    Character f where
  val := val
  hom := hom
  unit := unit

/-- Lift an `AddChar (HCFin hab) ℂ` to a `Character f` by composing
    with `HCFin.mk : Fin n → HCFin hab`. The hom property follows from
    `ψ.map_add_eq_mul'` and the unit-modulus from `addChar_normSq_one`. -/
def addCharToCharacter (hab : IsAbelianGroup f)
    (ψ : AddChar (HCFin hab) ℂ) : Character f where
  val a := ψ ⟨a⟩
  hom a b := by
    show ψ ⟨f.op a b⟩ = ψ ⟨a⟩ * ψ ⟨b⟩
    have hadd : (⟨f.op a b⟩ : HCFin hab) = ⟨a⟩ + ⟨b⟩ := rfl
    rw [hadd]
    exact ψ.map_add_eq_mul ⟨a⟩ ⟨b⟩
  unit a := HCFin.addChar_normSq_one hab ψ ⟨a⟩

/-! ## Step 4: orthogonality and CharacterBasis builder -/

variable {f : BinOp n}

/-- For two AddChars `ψ φ`, we have `(ψ - φ) a = ψ a * conj (φ a)`. -/
private theorem sub_apply_conj (hab : IsAbelianGroup f)
    (ψ φ : AddChar (HCFin hab) ℂ) (x : HCFin hab) :
    (ψ - φ) x = ψ x * starRingEnd ℂ (φ x) := by
  rw [AddChar.sub_apply']
  -- (ψ - φ) x = ψ x / φ x = ψ x * (φ x)⁻¹ = ψ x * conj(φ x).
  rw [div_eq_mul_inv, AddChar.inv_apply_eq_conj]

/-- Sum over `Fin n` of `f ⟨g⟩` equals sum over `HCFin hab` of `f x`. -/
private lemma sum_fin_eq_sum_hcfin (hab : IsAbelianGroup f)
    (h : HCFin hab → ℂ) :
    ∑ g : Fin n, h ⟨g⟩ = ∑ x : HCFin hab, h x :=
  Finset.sum_bij (fun g _ => (⟨g⟩ : HCFin hab))
    (fun _ _ => Finset.mem_univ _)
    (fun a _ b _ hab => HCFin.ext_iff.mp hab)
    (fun b _ => ⟨b.toFin, Finset.mem_univ _, rfl⟩)
    (fun _ _ => rfl)

/-- Pairwise orthogonality of two AddChars on `HCFin hab`:
    `(1/n) · Σ_g ψ(g) · star(φ(g)) = if ψ = φ then 1 else 0`. -/
theorem addChar_pairwise_orthogonality (hab : IsAbelianGroup f)
    (ψ φ : AddChar (HCFin hab) ℂ) :
    (1 / (n : ℂ)) * ∑ g : Fin n, ψ ⟨g⟩ * starRingEnd ℂ (φ ⟨g⟩) =
    if ψ = φ then 1 else 0 := by
  rw [sum_fin_eq_sum_hcfin hab (fun x => ψ x * starRingEnd ℂ (φ x))]
  -- Rewrite ψ x * conj(φ x) = (ψ - φ) x.
  have hsum_diff : ∑ x : HCFin hab, ψ x * starRingEnd ℂ (φ x) =
      ∑ x : HCFin hab, (ψ - φ) x := by
    apply Finset.sum_congr rfl
    intro x _
    rw [sub_apply_conj hab ψ φ x]
  rw [hsum_diff]
  -- Use Fintype.expect_eq_sum_div_card and AddChar.expect_eq_ite.
  have hcard : Fintype.card (HCFin hab) = n := HCFin.card_eq hab
  have h_expect_sum : 𝔼 x : HCFin hab, (ψ - φ) x =
      (∑ x : HCFin hab, (ψ - φ) x) / (Fintype.card (HCFin hab) : ℂ) :=
    Fintype.expect_eq_sum_div_card _
  have h_expect_ite : 𝔼 x : HCFin hab, (ψ - φ) x =
      if ψ - φ = 0 then 1 else 0 := AddChar.expect_eq_ite (ψ - φ)
  have h_eq : (∑ x : HCFin hab, (ψ - φ) x) / (Fintype.card (HCFin hab) : ℂ) =
      if ψ - φ = 0 then 1 else 0 := h_expect_sum ▸ h_expect_ite
  -- Convert (∑ ...) / n = if ... to (1/n) * (∑ ...) = if ...
  have hn_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hcard_C : ((Fintype.card (HCFin hab)) : ℂ) = (n : ℂ) := by
    exact_mod_cast hcard
  rw [show (1 / (n : ℂ)) * ∑ x : HCFin hab, (ψ - φ) x =
      (∑ x : HCFin hab, (ψ - φ) x) / (n : ℂ) from by ring]
  rw [← hcard_C, h_eq]
  -- ψ - φ = 0 ↔ ψ = φ.
  by_cases hψφ : ψ = φ
  · rw [hψφ]; simp; rfl
  · have h_ne : ψ - φ ≠ 0 := sub_ne_zero.mpr hψφ
    rw [if_neg h_ne, if_neg hψφ]

/-- The bijection `Fin n ≃ AddChar (HCFin hab) ℂ`, by Pontryagin duality. -/
noncomputable def addCharEquiv (hab : IsAbelianGroup f) :
    Fin n ≃ AddChar (HCFin hab) ℂ := by
  apply Fintype.equivOfCardEq
  rw [Fintype.card_fin, AddChar.card_eq, HCFin.card_eq]

/-- Completeness: `(1/n) Σ_ψ ψ(g) · conj(ψ(h)) = if g = h then 1 else 0`,
    where the sum is over all AddChars. -/
theorem addChar_completeness (hab : IsAbelianGroup f) (g h : Fin n) :
    (1 / (n : ℂ)) * ∑ ψ : AddChar (HCFin hab) ℂ,
      ψ ⟨g⟩ * starRingEnd ℂ (ψ ⟨h⟩) =
    if g = h then 1 else 0 := by
  -- ψ ⟨g⟩ * conj (ψ ⟨h⟩) = ψ (⟨g⟩ - ⟨h⟩).
  have h_step : ∀ ψ : AddChar (HCFin hab) ℂ,
      ψ ⟨g⟩ * starRingEnd ℂ (ψ ⟨h⟩) = ψ (⟨g⟩ - ⟨h⟩) := by
    intro ψ
    rw [← AddChar.inv_apply_eq_conj]
    rw [show (⟨g⟩ : HCFin hab) - ⟨h⟩ = ⟨g⟩ + (-⟨h⟩) from sub_eq_add_neg _ _]
    rw [show ψ (⟨g⟩ + (-⟨h⟩ : HCFin hab)) = ψ ⟨g⟩ * ψ (-⟨h⟩) from
      AddChar.map_add_eq_mul ψ ⟨g⟩ (-⟨h⟩)]
    rw [show ψ (-(⟨h⟩ : HCFin hab)) = (ψ ⟨h⟩)⁻¹ from AddChar.map_neg_eq_inv ψ ⟨h⟩]
  rw [Finset.sum_congr rfl (fun ψ _ => h_step ψ)]
  -- ∑_ψ, ψ (⟨g⟩ - ⟨h⟩) = if ⟨g⟩ - ⟨h⟩ = 0 then |HCFin hab| else 0.
  rw [AddChar.sum_apply_eq_ite (⟨g⟩ - ⟨h⟩ : HCFin hab)]
  rw [HCFin.card_eq hab]
  -- Now the goal is: (1/n) * (if ⟨g⟩ - ⟨h⟩ = 0 then n else 0) = if g = h then 1 else 0.
  have hn_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have h_iff : ((⟨g⟩ : HCFin hab) - ⟨h⟩ = 0) ↔ (g = h) := by
    constructor
    · intro hh
      have : (⟨g⟩ : HCFin hab) = ⟨h⟩ := by
        have := sub_eq_zero.mp hh
        exact this
      exact HCFin.ext_iff.mp this
    · intro hh; subst hh; simp
  by_cases h_gh : g = h
  · rw [if_pos h_gh, if_pos (h_iff.mpr h_gh)]
    field_simp
  · rw [if_neg h_gh, if_neg (fun h => h_gh (h_iff.mp h))]
    simp

/-- The `CharacterBasis` built from `IsAbelianGroup f`. -/
noncomputable def characterBasis (hab : IsAbelianGroup f) :
    CharacterBasis f where
  chars i := addCharToCharacter hab (addCharEquiv hab i)
  orth i j := by
    show (1 / (n : ℂ)) *
        ∑ g : Fin n, (addCharEquiv hab i) ⟨g⟩ *
          starRingEnd ℂ ((addCharEquiv hab j) ⟨g⟩) =
        if i = j then 1 else 0
    rw [addChar_pairwise_orthogonality hab (addCharEquiv hab i) (addCharEquiv hab j)]
    by_cases hij : i = j
    · rw [hij]; simp
    · have h_ne : addCharEquiv hab i ≠ addCharEquiv hab j := fun h =>
        hij ((addCharEquiv hab).injective h)
      rw [if_neg h_ne, if_neg hij]
  comp g h := by
    show (1 / (n : ℂ)) *
        ∑ i : Fin n, (addCharEquiv hab i) ⟨g⟩ *
          starRingEnd ℂ ((addCharEquiv hab i) ⟨h⟩) =
        if g = h then 1 else 0
    -- Sum over Fin n via the equiv equals sum over AddChar.
    rw [show ∑ i : Fin n, (addCharEquiv hab i) ⟨g⟩ *
          starRingEnd ℂ ((addCharEquiv hab i) ⟨h⟩) =
        ∑ ψ : AddChar (HCFin hab) ℂ, ψ ⟨g⟩ * starRingEnd ℂ (ψ ⟨h⟩) from
        Equiv.sum_comp (addCharEquiv hab)
          (fun ψ => ψ ⟨g⟩ * starRingEnd ℂ (ψ ⟨h⟩))]
    exact addChar_completeness hab g h

/-! ## Constructive abelian factorization via characterBasis -/

/-- For abelian `f`, the diagonal representation built from the canonical
    `characterBasis` gives a valid factorization. -/
theorem characterBasis_diagRep_factorizes (hab : IsAbelianGroup f) :
    let cb := characterBasis hab
    let Θ : HCParams n := ⟨diagRep cb.chars, diagRep cb.chars,
      fun g => (diagRep cb.chars g).conjTranspose⟩
    Factorizes Θ f := by
  let cb := characterBasis hab
  exact diagRep_factorizes cb.chars cb.orth cb.comp

/-- Each `diagRep` slice from `characterBasis` is unitary. -/
theorem characterBasis_diagRep_unitary (hab : IsAbelianGroup f) (g : Fin n) :
    let cb := characterBasis hab
    diagRep cb.chars g * (diagRep cb.chars g).conjTranspose = 1 := by
  let cb := characterBasis hab
  exact diagRep_unitary cb.chars g

/-- `frobNormSq (diagRep chars g) = 1` for any `chars` derived from a
    unit-modulus characterBasis. -/
theorem frobNormSq_diagRep (chars : Fin n → Character f) (g : Fin n) :
    frobNormSq (diagRep chars g) = 1 :=
  frobNormSq_unitary_eq_one _ (diagRep_unitary chars g)

/-- The collinear identity idA for diagRep: `B · C = A^H` (T/α = 1).
    Holds for `c = f.op a b` and abelian/group `f`. -/
theorem diagRep_collinearA (chars : Fin n → Character f) (a b : Fin n) :
    let c := f.op a b
    diagRep chars b * (diagRep chars c).conjTranspose =
    (diagRep chars a).conjTranspose := by
  intro c
  simp only [diagRep, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, Pi.star_def]
  congr 1
  funext i
  -- Goal: chars i .val b * star (chars i .val c) = star (chars i .val a)
  -- Use chars.hom: chars i .val c = chars i .val a * chars i .val b
  have hhom : (chars i).val c = (chars i).val a * (chars i).val b :=
    (chars i).hom a b
  rw [hhom]
  -- star (a · b) = star a · star b (in commutative ℂ).
  rw [show star ((chars i).val a * (chars i).val b) =
    star ((chars i).val a) * star ((chars i).val b) from by
    simp [mul_comm]]
  -- Goal: val b * (star val a · star val b) = star val a
  -- val b · star val b = 1 by unit modulus.
  have hunit : (chars i).val b * star ((chars i).val b) = 1 := by
    show (chars i).val b * starRingEnd ℂ ((chars i).val b) = 1
    rw [Complex.mul_conj, (chars i).unit b, Complex.ofReal_one]
  rw [show (chars i).val b * (star ((chars i).val a) * star ((chars i).val b)) =
      ((chars i).val b * star ((chars i).val b)) * star ((chars i).val a) from by ring]
  rw [hunit, one_mul]

/-- The collinear identity idB for diagRep: `C · A = B^H` (T/β = 1). -/
theorem diagRep_collinearB (chars : Fin n → Character f) (a b : Fin n) :
    let c := f.op a b
    (diagRep chars c).conjTranspose * diagRep chars a =
    (diagRep chars b).conjTranspose := by
  intro c
  simp only [diagRep, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, Pi.star_def]
  congr 1
  funext i
  have hhom : (chars i).val c = (chars i).val a * (chars i).val b :=
    (chars i).hom a b
  rw [hhom]
  rw [show star ((chars i).val a * (chars i).val b) =
    star ((chars i).val a) * star ((chars i).val b) from by simp [mul_comm]]
  have hunit : (chars i).val a * star ((chars i).val a) = 1 := by
    show (chars i).val a * starRingEnd ℂ ((chars i).val a) = 1
    rw [Complex.mul_conj, (chars i).unit a, Complex.ofReal_one]
  rw [show star ((chars i).val a) * star ((chars i).val b) * (chars i).val a =
      ((chars i).val a * star ((chars i).val a)) * star ((chars i).val b) from by ring]
  rw [hunit, one_mul]

/-- The collinear identity idC for diagRep with `Θ.C c := (diagRep c)^H`:
    `A · B = (Θ.C c)^H = diagRep c` (T/γ = 1). -/
theorem diagRep_collinearC (chars : Fin n → Character f) (a b : Fin n) :
    let c := f.op a b
    diagRep chars a * diagRep chars b =
    ((diagRep chars c).conjTranspose).conjTranspose := by
  intro c
  rw [Matrix.conjTranspose_conjTranspose]
  exact diagRep_hom chars a b

/-- The diagRep-characterBasis Theta satisfies PerfectCollinearity. -/
theorem characterBasis_diagRep_perfectCollinearity (hab : IsAbelianGroup f) :
    let cb := characterBasis hab
    let Θ : HCParams n := ⟨diagRep cb.chars, diagRep cb.chars,
      fun g => (diagRep cb.chars g).conjTranspose⟩
    PerfectCollinearity Θ f := by
  let cb := characterBasis hab
  set Θ : HCParams n := ⟨diagRep cb.chars, diagRep cb.chars,
    fun g => (diagRep cb.chars g).conjTranspose⟩ with hΘ_def
  have hfeas : Factorizes Θ f := characterBasis_diagRep_factorizes hab
  have hnd : Nondegenerate Θ := {
    A_pos := fun a => by
      show frobNormSq (diagRep cb.chars a) ≠ 0
      rw [frobNormSq_diagRep]; exact one_ne_zero,
    B_pos := fun b => by
      show frobNormSq (diagRep cb.chars b) ≠ 0
      rw [frobNormSq_diagRep]; exact one_ne_zero,
    C_pos := fun c => by
      show frobNormSq ((diagRep cb.chars c).conjTranspose) ≠ 0
      rw [frobNormSq_conjTranspose, frobNormSq_diagRep]; exact one_ne_zero }
  -- T = hcProduct Θ a b (f.op a b) = 1 by Factorizes.
  have hT_one : ∀ a b : Fin n, hcProduct Θ a b (f.op a b) = 1 := by
    intro a b
    have := hfeas a b (f.op a b)
    rwa [structureTensor, if_pos rfl] at this
  rw [perfectCollinearity_iff_identities Θ f hnd]
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    show diagRep cb.chars b * (diagRep cb.chars (f.op a b)).conjTranspose =
        (hcProduct Θ a b (f.op a b) / frobNormSq (diagRep cb.chars a)) •
          (diagRep cb.chars a).conjTranspose
    rw [hT_one, frobNormSq_diagRep, div_one, one_smul]
    exact diagRep_collinearA cb.chars a b
  · intro a b
    show (diagRep cb.chars (f.op a b)).conjTranspose * diagRep cb.chars a =
        (hcProduct Θ a b (f.op a b) / frobNormSq (diagRep cb.chars b)) •
          (diagRep cb.chars b).conjTranspose
    rw [hT_one, frobNormSq_diagRep, div_one, one_smul]
    exact diagRep_collinearB cb.chars a b
  · intro a b
    show diagRep cb.chars a * diagRep cb.chars b =
        (hcProduct Θ a b (f.op a b) /
          frobNormSq ((diagRep cb.chars (f.op a b)).conjTranspose)) •
          ((diagRep cb.chars (f.op a b)).conjTranspose).conjTranspose
    rw [hT_one, frobNormSq_conjTranspose, frobNormSq_diagRep, div_one, one_smul]
    exact diagRep_collinearC cb.chars a b

/-- **The diagRep-characterBasis Theta is a UnitaryCollinear factorization.** -/
theorem characterBasis_diagRep_unitaryCollinear (hab : IsAbelianGroup f) :
    let cb := characterBasis hab
    let Θ : HCParams n := ⟨diagRep cb.chars, diagRep cb.chars,
      fun g => (diagRep cb.chars g).conjTranspose⟩
    UnitaryCollinear Θ f := by
  let cb := characterBasis hab
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact characterBasis_diagRep_perfectCollinearity hab
  · exact characterBasis_diagRep_factorizes hab
  · intro a; exact diagRep_unitary cb.chars a
  · intro b; exact diagRep_unitary cb.chars b
  · intro c
    show (diagRep cb.chars c).conjTranspose *
        ((diagRep cb.chars c).conjTranspose).conjTranspose = 1
    rw [Matrix.conjTranspose_conjTranspose]
    exact mul_eq_one_comm.mp (diagRep_unitary cb.chars c)

/-- **Explicit objective value.** The diagRep-characterBasis Θ achieves
    `ℋ(Θ).re = 3n²`, the global minimum on the collinear manifold. -/
theorem characterBasis_diagRep_objective_value (hab : IsAbelianGroup f) :
    let cb := characterBasis hab
    let Θ : HCParams n := ⟨diagRep cb.chars, diagRep cb.chars,
      fun g => (diagRep cb.chars g).conjTranspose⟩
    (objective Θ f).re = 3 * (n : ℝ) ^ 2 :=
  uc_objective_value _ _ (characterBasis_diagRep_unitaryCollinear hab)

/-- **Existence of the abelian optimum via diagRep-characterBasis.**
    For any abelian `f`, there exists a unitary collinear factorisation
    achieving `ℋ = 3n²`, constructed via Pontryagin duality. -/
theorem abelian_admits_diagRep_optimum (hab : IsAbelianGroup f) :
    ∃ Θ_opt : HCParams n,
      UnitaryCollinear Θ_opt f ∧
      (objective Θ_opt f).re = 3 * (n : ℝ) ^ 2 := by
  let cb := characterBasis hab
  refine ⟨⟨diagRep cb.chars, diagRep cb.chars,
    fun g => (diagRep cb.chars g).conjTranspose⟩, ?_, ?_⟩
  · exact characterBasis_diagRep_unitaryCollinear hab
  · exact characterBasis_diagRep_objective_value hab

/-- For an abelian group `f`, there exists a feasible Θ achieving `ℋ = 3n²`.
    Direct corollary of `abelian_admits_diagRep_optimum` (which produces a
    UnitaryCollinear factorisation), unwrapping `Factorizes`. -/
theorem abelian_optimum_attained_feasible (hab : IsAbelianGroup f) :
    ∃ Θ : HCParams n, Factorizes Θ f ∧
      (objective Θ f).re = 3 * (n : ℝ) ^ 2 := by
  obtain ⟨Θ, huc, hH⟩ := abelian_admits_diagRep_optimum hab
  exact ⟨Θ, huc.feasible, hH⟩

/-- For an abelian group `f`, the Pontryagin/character-basis construction
    produces a Nondegenerate factorisation. (UC slices have unit Frobenius
    norm, hence nonzero.) -/
theorem abelian_admits_diagRep_nondegenerate (hab : IsAbelianGroup f) :
    ∃ Θ : HCParams n, Nondegenerate Θ ∧ UnitaryCollinear Θ f := by
  obtain ⟨Θ, huc, _⟩ := abelian_admits_diagRep_optimum hab
  refine ⟨Θ, ?_, huc⟩
  refine {
    A_pos := fun a => ?_,
    B_pos := fun b => ?_,
    C_pos := fun c => ?_ }
  · rw [frobNormSq_unitary_eq_one _ (huc.unitaryA a)]; exact one_ne_zero
  · rw [frobNormSq_unitary_eq_one _ (huc.unitaryB b)]; exact one_ne_zero
  · rw [frobNormSq_unitary_eq_one _ (huc.unitaryC c)]; exact one_ne_zero

end IsAbelianGroup

end
