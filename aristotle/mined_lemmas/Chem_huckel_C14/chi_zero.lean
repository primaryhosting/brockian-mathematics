import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Finset Complex

set_option maxHeartbeats 1000000

namespace Chem

/-- A primitive 14-th root of unity. -/

lemma chi_zero : chi 0 = 1 := by simp [chi]

