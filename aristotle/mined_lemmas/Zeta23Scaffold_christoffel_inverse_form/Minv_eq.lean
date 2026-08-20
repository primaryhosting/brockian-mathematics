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

/-- The `3 × 3` sine-kernel Hankel matrix. -/

lemma Minv_eq : M⁻¹ = Minv := by
  refine Matrix.inv_eq_right_inv M_mul_Minv

/-- Inverse-matrix cross-check: `M` is invertible (its determinant is `5/108 ≠ 0`) and
`(M⁻¹)₀₀ = 36/5`, so `1 / (eᵀ₀ M⁻¹ e₀) = 5/36`, matching the determinant-ratio
Christoffel value `Λ₂(0;1) = 5/36`. -/
