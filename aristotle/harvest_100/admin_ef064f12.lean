/- (Lean requires `import` to precede any module docstring, so the mandated header
   comment is reproduced below as a block comment and again after the import.)
# Hankel Christoffel 13 18
Category: B Christoffel
Target: Zeta23Scaffold.hankel_christoffel_13_18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hankel Christoffel 13 18
Category: B Christoffel
Target: Zeta23Scaffold.hankel_christoffel_13_18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Zeta23Scaffold

/-- The `3 × 3` Hankel (moment) matrix `(m_{i+j})_{0 ≤ i,j ≤ 2}` of the sine-kernel
moment sequence `m_0, …, m_4 = 1, 1, 4/3, 2, 13/4` at `λ = 1`. -/
def hankelM : Matrix (Fin 3) (Fin 3) Rat :=
  !![1, 1, 4/3; 1, 4/3, 2; 4/3, 2, 13/4]

/-- The trailing `2 × 2` Hankel minor `(m_{i+j})_{1 ≤ i,j ≤ 2}`. -/
def hankelMinor : Matrix (Fin 2) (Fin 2) Rat :=
  !![4/3, 2; 2, 13/4]

/-- The Christoffel function value `Λ₂(0;1)`, computed as the Hankel determinant ratio. -/
def Lambda : Rat := hankelM.det / hankelMinor.det

/-- **Hankel Christoffel 13/18.**
(a) the `3 × 3` sine-kernel Hankel determinant is `5/108`;
(b) the Christoffel function value `Λ₂(0;1) = M.det / minor.det` equals `5/36`;
(c) `1 - Λ = 31/36`;
(d) the ladder assembly `2 * (1 - Λ) - 1 = 13/18`. -/
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
    rw [Lambda, hM, hm]
    norm_num
  refine ⟨hM, hL, ?_, ?_⟩ <;> rw [hL] <;> norm_num

end Zeta23Scaffold

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

