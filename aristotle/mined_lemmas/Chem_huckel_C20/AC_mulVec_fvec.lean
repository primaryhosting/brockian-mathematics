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

lemma AC_mulVec_fvec (k : ℕ) (hk : k ≤ 20) :
    AC *ᵥ fvec k = (w ^ k + w ^ (20 - k)) • fvec k := by
  rw [AC_eq, Matrix.add_mulVec, S_mulVec_fvec, pow_mulVec (S_mulVec_fvec k) 19,
    w_pow_nineteen k hk, add_smul]

/-! ## The annihilating polynomial -/

/-- The polynomial `∏ (X - (wᵏ + w⁻ᵏ))`, whose roots are the claimed eigenvalues. -/
