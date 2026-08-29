/-
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 4000000

namespace Chem

/-- A primitive 8-th root of unity. -/

lemma zeta_pow_mul_eight (k : ℕ) : zeta ^ (k * 8) = 1 := by
  simpa using zeta_pow_mod (k * 8) 0 (by omega)

