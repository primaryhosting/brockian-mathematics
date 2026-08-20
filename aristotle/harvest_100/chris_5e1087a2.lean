/-
# Hankel Christoffel 13 18
Category: B Christoffel
Target: Zeta23Scaffold.hankel_christoffel_13_18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

/-- The 3×3 rational Hankel (moment) matrix `(m_{i+j})_{0 ≤ i,j ≤ 2}` built from the
sine-kernel moment sequence `m_0, …, m_4 = 1, 1, 4/3, 2, 13/4` at `λ = 1`. -/
def hankelM : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, 1, 4/3; 1, 4/3, 2; 4/3, 2, 13/4]

/-- The shifted 2×2 Hankel minor `(m_{i+j+2})_{0 ≤ i,j ≤ 1}`. -/
def hankelMinor : Matrix (Fin 2) (Fin 2) ℚ :=
  !![4/3, 2; 2, 13/4]

/-- The Christoffel value `Λ₂(0;1)`, computed as the Hankel determinant ratio. -/
def Lambda : ℚ := hankelM.det / hankelMinor.det

/-- **Hankel–Christoffel `13/18` rung.**
For the sine-kernel moment matrix at `λ = 1`:
(a) `det M = 5/108`;
(b) the Christoffel function `Λ₂(0;1) = det M / det (minor) = 5/36`;
(c) `1 - Λ = 31/36`;
(d) the ladder assembly `2·(1 - Λ) - 1 = 13/18`. -/
theorem hankel_christoffel_13_18 :
    hankelM.det = 5/108 ∧ Lambda = 5/36 ∧ (1 - Lambda) = 31/36 ∧
      2 * (1 - Lambda) - 1 = 13/18 := by
  have hM : hankelM.det = 5/108 := by
    simp [hankelM, Matrix.det_fin_three]
    norm_num
  have hm : hankelMinor.det = 1/3 := by
    simp [hankelMinor, Matrix.det_fin_two]
    norm_num
  have hL : Lambda = 5/36 := by
    rw [Lambda, hM, hm]; norm_num
  refine ⟨hM, hL, ?_, ?_⟩ <;> rw [hL] <;> norm_num

end Zeta23Scaffold

