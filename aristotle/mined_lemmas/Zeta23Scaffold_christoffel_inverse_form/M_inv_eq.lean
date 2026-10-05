import Mathlib
/-!
# Christoffel Inverse Form
Category: B Christoffel
Target: Zeta23Scaffold.christoffel_inverse_form
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Zeta23Scaffold

/-- The sine-kernel Hankel matrix of order 3. -/

lemma M_inv_eq : M⁻¹ = Minv := Matrix.inv_eq_right_inv M_mul_Minv

/-- Inverse-matrix cross-check for the sine-kernel Hankel matrix: its determinant is
`5/108` (hence nonzero, so the matrix is invertible), and `(M⁻¹) 0 0 = 36/5`, so that
`1 / (e₀ᵀ M⁻¹ e₀) = 5/36`, agreeing with the determinant-ratio Christoffel value. -/
