/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Polynomial SimpleGraph

/-- The adjacency matrix of the cycle graph `C₁₆` (the Hückel matrix of a
16-membered annulene, with `α = 0`, `β = 1`). -/

theorem C16_eq_conj :
    C16 = dft16 * Matrix.diagonal huckelLevel * dft16⁻¹ := by
  rw [← C16_mul_dft16, Matrix.mul_nonsing_inv_cancel_right]
  exact (Matrix.isUnit_iff_isUnit_det _).mp dft16_isUnit

