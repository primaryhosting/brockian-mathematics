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

lemma M_det : M.det = 5/108 := by
  simp [M, Matrix.det_fin_three]
  norm_num

