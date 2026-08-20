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

theorem sum_vertexCharacter_sr [NeZero n] :
    ∑ i : ZMod n, vertexCharacter n (.sr i) = n := by
  have key : ∀ i : ZMod n,
      (univ.filter fun x : ZMod n => vertexPerm n (.sr i) x = x)
        = univ.filter fun x : ZMod n => -2 * x = i := by
    intro i
    apply Finset.filter_congr
    intro x _
    simp only [vertexPerm_sr]
    constructor
    · intro h; linear_combination h
    · intro h; linear_combination h
  have hcard : (univ : Finset (ZMod n)).card
      = ∑ i : ZMod n, (univ.filter fun x : ZMod n => -2 * x = i).card :=
    Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (-2 * x))
  calc ∑ i : ZMod n, vertexCharacter n (.sr i)
      = ∑ i : ZMod n, (univ.filter fun x : ZMod n => -2 * x = i).card := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [vertexCharacter_eq_filter, key i]
    _ = (univ : Finset (ZMod n)).card := hcard.symm
    _ = n := by simp [ZMod.card]

