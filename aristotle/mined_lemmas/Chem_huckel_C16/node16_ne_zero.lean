/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Matrix Complex

/-- A primitive 16-th root of unity. -/

lemma node16_ne_zero (k : Fin 16) : node16 k ≠ 0 := by
  intro h
  have := node16_pow_16 k
  rw [h] at this
  norm_num at this

/-- For a 16-th root of unity, the exponent may be taken in `Fin 16`. -/
