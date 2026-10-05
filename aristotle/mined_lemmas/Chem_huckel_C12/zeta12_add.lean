import Mathlib

/-!
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Complex Polynomial Matrix Finset

/-- The primitive 12-th root of unity `exp(2πi/12)`. -/

lemma zeta12_add (a b : ZMod 12) : zeta12 (a + b) = zeta12 a * zeta12 b := by
  simp only [zeta12, ← pow_add]
  rw [ZMod.val_add, w12_pow_mod]

