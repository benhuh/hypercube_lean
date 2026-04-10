import HyperCubeGroup.Basic
open Matrix BigOperators Finset Complex ComplexConjugate

noncomputable section
variable {n : ℕ} [NeZero n]
variable (V : Matrix (Fin n) (Fin n) ℂ) (hV : IsUnit V)

#check @nonsing_inv_mul (Fin n) ℂ _ _ _
-- example : V⁻¹ * V = 1 := nonsing_inv_mul V (isUnit_iff_isUnit_det.mp hV)
