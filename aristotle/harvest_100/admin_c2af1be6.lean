import Mathlib

/-!
# Hankel Christoffel 13 18
Category: B Christoffel
Target: Zeta23Scaffold.hankel_christoffel_13_18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Zeta23Scaffold

/-- The `3 × 3` Hankel (moment) matrix `(m_{i+j})_{0 ≤ i,j ≤ 2}` of the sine-kernel
moment sequence `m_0, …, m_4 = 1, 1, 4/3, 2, 13/4` at `λ = 1`. -/
def hankelM : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 1, 4/3; 1, 4/3, 2; 4/3, 2, 13/4]

/-- The trailing `2 × 2` Hankel minor `(m_{i+j})_{1 ≤ i,j ≤ 2}`. -/
def hankelMinor : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(4:ℚ)/3, 2; 2, 13/4]

/-- The Christoffel function value `Λ₂(0;1)`, computed as the Hankel determinant ratio. -/
def Lambda : ℚ := hankelM.det / hankelMinor.det

/-- (a) The `3 × 3` Hankel determinant equals `5/108`. -/
theorem hankelM_det : hankelM.det = 5 / 108 := by
  rw [hankelM]
  simp [Matrix.det_fin_three]
  norm_num

/-- The trailing `2 × 2` Hankel minor has determinant `1/3`. -/
theorem hankelMinor_det : hankelMinor.det = 1 / 3 := by
  rw [hankelMinor]
  simp [Matrix.det_fin_two]
  norm_num

/-- (b) `Λ₂(0;1) = 5/36`. -/
theorem Lambda_eq : Lambda = 5 / 36 := by
  rw [Lambda, hankelM_det, hankelMinor_det]
  norm_num

/-- (c) `1 - Λ₂(0;1) = 31/36`. -/
theorem one_sub_Lambda : 1 - Lambda = 31 / 36 := by
  rw [Lambda_eq]; norm_num

/-- (d) The ladder assembly: `2 * (1 - Λ₂(0;1)) - 1 = 13/18`. -/
theorem ladder_assembly : 2 * (1 - Lambda) - 1 = 13 / 18 := by
  rw [one_sub_Lambda]; norm_num

/-- **Main target.** The exact-arithmetic core of the conditional `13/18` rung:
the `3 × 3` sine-kernel Hankel determinant is `5/108`, the Christoffel value
`Λ₂(0;1) = M.det / minor.det` equals `5/36`, hence `1 - Λ = 31/36` and the ladder
assembly `2 * (1 - Λ) - 1` equals `13/18`. -/
theorem hankel_christoffel_13_18 :
    hankelM.det = 5 / 108 ∧
    Lambda = 5 / 36 ∧
    1 - Lambda = 31 / 36 ∧
    2 * (1 - Lambda) - 1 = 13 / 18 :=
  ⟨hankelM_det, Lambda_eq, one_sub_Lambda, ladder_assembly⟩

end Zeta23Scaffold

