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

lemma omega19_ne_zero : omega19 ≠ 0 := by
  intro h
  have := omega19_pow
  rw [h] at this
  norm_num at this

/-- The discrete Fourier transform matrix of size 19. -/
