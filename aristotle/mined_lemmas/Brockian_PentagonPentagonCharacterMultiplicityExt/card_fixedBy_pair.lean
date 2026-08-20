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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-- The natural action of the dihedral group `DihedralGroup n` on the `n` vertices of a regular
`n`-gon, the vertices being modelled by `ZMod n`.  The rotation `r i` sends a vertex `x` to
`x - i`, and the reflection `sr i` sends `x` to `i - x`. -/

lemma card_fixedBy_pair (n : ℕ) [NeZero n] (g : DihedralGroup n) :
    Fintype.card (MulAction.fixedBy (ZMod n × ZMod n) g) = (ngonChar n g) ^ 2 := by
  classical
  rw [Fintype.card_congr (fixedByPairEquiv n g), Fintype.card_prod, ngonChar, sq]

/-- **Orbits on ordered pairs of vertices.**  The dihedral group `D_n` acting diagonally on ordered
pairs of vertices of the regular `n`-gon has `(n + χ(sr 0))/2` orbits, where `χ(sr 0) ∈ {1, 2}`
is the number of solutions of `2d = 0` in `ZMod n`. -/
