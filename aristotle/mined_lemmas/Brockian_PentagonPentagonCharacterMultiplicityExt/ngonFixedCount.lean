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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

open MulAction

/-!
## The geometric action of the dihedral group on the vertices of an `n`-gon

We model the vertices of a regular `n`-gon by `ZMod n`.  The rotation `r i` moves the vertex
`x` to `x - i` and the reflection `sr i` moves the vertex `x` to `i - x`.
-/

/-- The action of `DihedralGroup n` on the vertex set `ZMod n` of the regular `n`-gon. -/

noncomputable def ngonFixedCount (n : ℕ) (g : DihedralGroup n) : ℕ :=
  Nat.card (MulAction.fixedBy (ZMod n) g)

/-- There is exactly one orbit of the dihedral group on the vertices of the `n`-gon. -/
