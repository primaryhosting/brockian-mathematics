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

lemma permChar_r_ne_zero (n : ℕ) [NeZero n] {i : ZMod n} (hi : i ≠ 0) :
    permChar n (r i) = 0 := by
  rw [permChar, Fintype.card_eq_zero_iff]
  refine ⟨fun x => ?_⟩
  have hx : (x : ZMod n) - i = x := x.2
  exact hi (by linear_combination -hx)

/-- For odd `n` the element `2` is invertible in `ZMod n`. -/
