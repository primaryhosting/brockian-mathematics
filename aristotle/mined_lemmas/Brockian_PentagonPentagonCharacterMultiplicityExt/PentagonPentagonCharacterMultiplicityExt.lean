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

theorem PentagonPentagonCharacterMultiplicityExt (n : ℕ) [NeZero n] :
    (∑ g : DihedralGroup n, vertexCharacter n g) = 2 * n ∧
    (∑ g : DihedralGroup n, vertexCharacter n g) = Fintype.card (DihedralGroup n) ∧
    (∑ g : DihedralGroup n, vertexCharacter n g) / Fintype.card (DihedralGroup n) = 1 := by
  have hcard : Fintype.card (DihedralGroup n) = 2 * n := DihedralGroup.card
  refine ⟨sum_vertexCharacter, by rw [sum_vertexCharacter, hcard], ?_⟩
  rw [sum_vertexCharacter, hcard, Nat.div_self]
  have : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  omega

/-- The pentagon case `n = 5`: the vertex character of `D₅` sums to `10 = |D₅|`. -/
