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

set_option maxHeartbeats 1000000

namespace Zeta23Scaffold

/-- The `3 × 3` sine-kernel Hankel matrix. -/

theorem christoffelHankelMatrix_det :
    christoffelHankelMatrix.det = 5/108 := by
  simp [christoffelHankelMatrix, Matrix.det_fin_three]
  norm_num

