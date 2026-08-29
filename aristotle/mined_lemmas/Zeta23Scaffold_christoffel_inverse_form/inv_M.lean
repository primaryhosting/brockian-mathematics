/-
# Christoffel Inverse Form
Category: B Christoffel
Target: Zeta23Scaffold.christoffel_inverse_form
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000

namespace Zeta23Scaffold

/-- The 3×3 sine-kernel Hankel matrix. -/

theorem inv_M : M⁻¹ = Minv := Matrix.inv_eq_right_inv M_mul_Minv

/-- Inverse-matrix cross-check for the Christoffel function: `M` is invertible
(`det M = 5/108 ≠ 0`) and `(M⁻¹)₀₀ = 36/5`, so `1 / (e₀ᵀ M⁻¹ e₀) = 5/36`,
agreeing with the determinant-ratio Christoffel value. -/
