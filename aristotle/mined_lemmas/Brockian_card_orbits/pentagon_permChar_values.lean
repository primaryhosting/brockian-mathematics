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

theorem pentagon_permChar_values :
    permChar 5 (r 0) = 5 ∧ (∀ i : ZMod 5, i ≠ 0 → permChar 5 (r i) = 0) ∧
      (∀ i : ZMod 5, permChar 5 (sr i) = 1) :=
  ⟨permChar_r_zero 5, fun _ hi => permChar_r_ne_zero 5 hi,
    fun i => permChar_sr_of_odd 5 (by decide) i⟩

/-- The pentagon case of the main theorem. -/
