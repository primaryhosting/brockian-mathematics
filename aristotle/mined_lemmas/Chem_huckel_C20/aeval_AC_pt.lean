import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Finset Polynomial

set_option maxHeartbeats 1000000

/-! ## Generalities on eigenvalues of matrices -/

/-- A scalar `μ` is an eigenvalue of `M` iff `M - μ • 1` is singular. -/

lemma aeval_AC_pt : aeval AC pt = 0 := by
  obtain ⟨c, hc⟩ := key_dvd
  have h1 : aeval S (pt.comp (X + X ^ 19)) = aeval AC pt := by
    rw [Polynomial.aeval_comp]
    simp [AC_eq]
  rw [← h1, hc, map_mul]
  have : aeval S (X ^ 20 - 1 : ℂ[X]) = 0 := by
    simp [S_pow_twenty]
  rw [this, zero_mul]

/-! ## The main results -/

