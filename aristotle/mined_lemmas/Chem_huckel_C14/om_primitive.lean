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

lemma om_primitive : IsPrimitiveRoot om 14 := by
  have := Complex.isPrimitiveRoot_exp 14 (by norm_num)
  simpa [om, mul_comm, mul_assoc, mul_left_comm] using this

