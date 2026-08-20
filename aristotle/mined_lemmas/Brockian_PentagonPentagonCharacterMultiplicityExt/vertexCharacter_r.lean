/-
# Pentagon Pentagon Character Multiplicity Ext
Category: Brockian Corpus
Target: Brockian.PentagonPentagonCharacterMultiplicityExt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pentagon Pentagon Character Multiplicity Ext
Category: Brockian Corpus
Target: Brockian.PentagonPentagonCharacterMultiplicityExt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

open Finset

variable {n : ℕ}

/-- The permutation action of the dihedral group `DihedralGroup n` on the `n` vertices of the
regular `n`-gon (labelled by `ZMod n`): the rotation `r i` sends a vertex `x` to `x + i`, and the
reflection `sr i` sends `x` to `-i - x`. -/

theorem vertexCharacter_r [NeZero n] (i : ZMod n) :
    vertexCharacter n (.r i) = if i = 0 then n else 0 := by
  rw [vertexCharacter_eq_filter]
  by_cases hi : i = 0
  · subst hi
    simp [ZMod.card]
  · simp only [vertexPerm_r, hi, if_false]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _
    simpa using fun h => hi (by linear_combination h)

/-- Summed over all rotations, the character contributes `n`. -/
