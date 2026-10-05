/-
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/-- The adjacency matrix of the cycle graph `C₈`, indexed by `ZMod 8`
(vertex `i` is adjacent to `i + 1` and `i - 1`), with complex entries. -/

lemma succ_ne_pred (j : ZMod 8) : j + 1 ≠ j - 1 := by
  intro h
  have h2 : (2 : ZMod 8) = 0 := by linear_combination h
  exact absurd h2 (by decide)

/-- Applying the adjacency matrix of `C₈` to a vector sums the two neighbouring values. -/
