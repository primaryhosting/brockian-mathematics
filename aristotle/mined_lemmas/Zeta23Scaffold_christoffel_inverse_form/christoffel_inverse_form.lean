/-
# Christoffel Inverse Form
Category: B Christoffel
Target: Zeta23Scaffold.christoffel_inverse_form
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Christoffel Inverse Form
Category: B Christoffel
Target: Zeta23Scaffold.christoffel_inverse_form
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

/-- The 3×3 sine-kernel Hankel matrix of moments. -/

theorem christoffel_inverse_form :
    hankelM.det = 5/108 ∧ IsUnit hankelM.det ∧ hankelM⁻¹ 0 0 = 36/5 ∧
      (∑ i, ∑ j, (if i = 0 then (1:ℚ) else 0) * hankelM⁻¹ i j * (if j = 0 then (1:ℚ) else 0))⁻¹
        = 5/36 := by
  refine ⟨hankelM_det, ?_, ?_, ?_⟩
  · rw [hankelM_det]
    exact isUnit_iff_ne_zero.mpr (by norm_num)
  · rw [hankelM_inv_eq]; simp [hankelMinv]
  · rw [hankelM_inv_eq]
    simp [Fin.sum_univ_succ, hankelMinv]
    norm_num

end Zeta23Scaffold

