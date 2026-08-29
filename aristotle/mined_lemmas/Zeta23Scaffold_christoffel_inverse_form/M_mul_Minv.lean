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

lemma M_mul_Minv : M * Minv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M, Minv, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num

