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

lemma w_pow_twenty : w ^ 20 = 1 := w_primitive.pow_eq_one

/-- `w ^ n` only depends on `n % 20`. -/
