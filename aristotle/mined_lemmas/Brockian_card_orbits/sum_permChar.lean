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

lemma sum_permChar (n : ℕ) [NeZero n] :
    ∑ g : DihedralGroup n, permChar n g = 2 * n := by
  simp only [permChar]
  rw [MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group, card_orbits, one_mul,
    DihedralGroup.card]

/-!
## Explicit values of the permutation character

These are not needed for the main theorem, but they pin down the character concretely and
confirm that the setup is the intended one: a nontrivial rotation fixes no vertex, the
identity fixes all `n` of them, and (for odd `n`) every reflection fixes exactly one vertex.
-/

/-- The identity rotation fixes every vertex. -/
