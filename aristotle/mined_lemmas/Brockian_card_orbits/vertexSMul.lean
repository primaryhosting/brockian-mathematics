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

def vertexSMul {n : ℕ} : DihedralGroup n → ZMod n → ZMod n
  | r i, x => x - i
  | sr i, x => i - x

/-- The natural action of the dihedral group `DihedralGroup n` on the vertex set
`ZMod n` of the regular `n`-gon. -/
instance vertexAction (n : ℕ) : MulAction (DihedralGroup n) (ZMod n) where
  smul := vertexSMul
  one_smul x := by
    show vertexSMul (r 0) x = x
    simp [vertexSMul]
  mul_smul g h x := by
    cases g with
    | r i =>
      cases h with
      | r j =>
        show vertexSMul (r (i + j)) x = vertexSMul (r i) (vertexSMul (r j) x)
        simp [vertexSMul]; ring
      | sr j =>
        show vertexSMul (sr (j - i)) x = vertexSMul (r i) (vertexSMul (sr j) x)
        simp [vertexSMul]; ring
    | sr i =>
      cases h with
      | r j =>
        show vertexSMul (sr (i + j)) x = vertexSMul (sr i) (vertexSMul (r j) x)
        simp [vertexSMul]; ring
      | sr j =>
        show vertexSMul (r (j - i)) x = vertexSMul (sr i) (vertexSMul (sr j) x)
        simp [vertexSMul]; ring

