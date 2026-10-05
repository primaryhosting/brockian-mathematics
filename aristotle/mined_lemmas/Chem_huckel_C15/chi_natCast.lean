import Mathlib

/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

/-- The primitive 15-th root of unity `exp(2πi/15)`. -/

lemma chi_natCast (m : ℕ) : chi (m : ZMod 15) = zeta ^ m := by
  rw [chi, ZMod.val_natCast, zeta_pow_mod]

