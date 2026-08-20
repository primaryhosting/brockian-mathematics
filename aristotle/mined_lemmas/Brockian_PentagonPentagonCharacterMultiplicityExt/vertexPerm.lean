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

def vertexPerm (n : ℕ) : DihedralGroup n →* Equiv.Perm (ZMod n) where
  toFun g := match g with
    | .r i => Equiv.addRight i
    | .sr i => Equiv.subLeft (-i)
  map_one' := by
    apply Equiv.ext
    intro x
    show x + (0 : ZMod n) = x
    exact add_zero x
  map_mul' := by
    rintro (i | i) (j | j) <;> apply Equiv.ext <;> intro x <;>
      simp [Equiv.addRight, Equiv.subLeft, Equiv.Perm.mul_apply] <;> ring

@[simp]
