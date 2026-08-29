import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real
open Complex Matrix

namespace Chem

/-- A primitive 19-th root of unity. -/

lemma pow_pow_19 (v : ℂ) (hv : v ^ 19 = 1) (a : ℕ) : (v ^ a) ^ 19 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, hv, one_pow]

