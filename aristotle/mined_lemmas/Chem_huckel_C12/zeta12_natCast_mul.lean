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

lemma zeta12_natCast_mul (n : ℕ) (m : ZMod 12) :
    zeta12 ((n : ZMod 12) * m) = zeta12 m ^ n := by
  induction n with
  | zero => simpa using zeta12_zero
  | succ n ih =>
      have h : ((n + 1 : ℕ) : ZMod 12) * m = (n : ZMod 12) * m + m := by push_cast; ring
      rw [h, zeta12_add, ih, pow_succ]

