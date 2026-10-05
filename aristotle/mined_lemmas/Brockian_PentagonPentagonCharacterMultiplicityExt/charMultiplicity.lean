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

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

open DihedralGroup

/-! ## The action of the dihedral group on the vertices of the `n`-gon -/

/-- The action of `DihedralGroup n` on the `n` vertices of the regular `n`-gon,
whose vertices are labelled by `ZMod n`.  The rotation `r i` sends the vertex `x` to
`x - i` and the reflection `sr i` sends `x` to `i - x`. -/

noncomputable def charMultiplicity (n : ℕ) [NeZero n] (χ : DihedralGroup n → ℂ) : ℂ :=
  (1 / (2 * n)) * ∑ g : DihedralGroup n, vertexChar n g * (starRingEnd ℂ) (χ g)

/-- **Pentagon Pentagon Character Multiplicity Ext.**
For every regular `n`-gon (`n ≥ 1`), the permutation representation on the vertices contains
each two-dimensional character `χ_h` of the dihedral symmetry group with multiplicity exactly `1`,
and the trivial character with multiplicity exactly `1`.  For `n = 5` this is the classical
statement for the pentagon and the dihedral group `D₅`. -/
