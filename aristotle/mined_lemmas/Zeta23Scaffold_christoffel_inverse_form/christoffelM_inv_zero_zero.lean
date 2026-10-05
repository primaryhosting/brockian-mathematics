/-
# Christoffel Inverse Form
Category: B Christoffel
Target: Zeta23Scaffold.christoffel_inverse_form
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Scaffold

/-- The order-3 sine-kernel Hankel matrix. -/

theorem christoffelM_inv_zero_zero : christoffelM⁻¹ 0 0 = 36 / 5 := by
  rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_fin_three, christoffelM_det]
  simp [christoffelM]
  norm_num

/-- **Christoffel inverse form.** The sine-kernel Hankel matrix `M` is invertible
(its determinant is `5/108 ≠ 0`), the `(0,0)` entry of `M⁻¹` is `36/5`, and hence the
classical Christoffel value `1 / (e₀ᵀ M⁻¹ e₀)` equals `5/36`, matching the
determinant-ratio definition of `Λ₂(0;1)`. -/
