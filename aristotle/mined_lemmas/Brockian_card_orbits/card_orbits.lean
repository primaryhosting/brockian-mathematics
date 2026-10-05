-- (Lean 4 requires `import` lines to precede any module docstring, so the required
-- header comment appears immediately below the import.)
import Mathlib

/-!
# Pentagon Pentagon Character Multiplicity Ext
Category: Brockian Corpus
Target: Brockian.PentagonPentagonCharacterMultiplicityExt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

open DihedralGroup

namespace Brockian

/-!
## Setup: the dihedral group acting on the vertices of a regular `n`-gon

We model the vertices of the regular `n`-gon by `ZMod n`.  The dihedral group
`DihedralGroup n` acts on them, with the rotation `r i` translating by `-i` and the
reflection `sr i` acting by `x ↦ i - x`.  (The signs are dictated by Mathlib's
multiplication convention `r i * r j = r (i + j)`, `r i * sr j = sr (j - i)`,
`sr i * r j = sr (i + j)`, `sr i * sr j = r (j - i)`.)
-/

/-- The underlying map of the action of `DihedralGroup n` on the vertex set `ZMod n`
of the regular `n`-gon. -/

lemma card_orbits (n : ℕ) [NeZero n] :
    Fintype.card (Quotient (MulAction.orbitRel (DihedralGroup n) (ZMod n))) = 1 := by
  rw [Fintype.card_eq_one_iff]
  refine ⟨Quotient.mk _ (0 : ZMod n), ?_⟩
  intro y
  induction y using Quotient.inductionOn with
  | h a =>
    apply Quotient.sound
    refine ⟨r (0 - a), ?_⟩
    show (r (0 - a)) • (0 : ZMod n) = a
    rw [vertex_r_smul]; ring

/-!
## The permutation character

`permChar n g` is the value at `g` of the character of the permutation representation of
`DihedralGroup n` on the vertices of the `n`-gon, i.e. the number of vertices fixed by `g`.
-/

/-- The permutation character of the dihedral group acting on the vertices of the
regular `n`-gon: the number of vertices fixed by `g`. -/
