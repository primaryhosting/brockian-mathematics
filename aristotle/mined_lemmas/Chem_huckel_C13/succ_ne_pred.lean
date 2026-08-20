import Mathlib
/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Complex Matrix

namespace Chem

/-- A primitive 13-th root of unity. -/

lemma succ_ne_pred (i : ZMod 13) : (i + 1 : ZMod 13) ≠ i - 1 := by
  intro h
  have h2 : (2 : ZMod 13) = 0 := by linear_combination h
  exact absurd h2 (by decide)

