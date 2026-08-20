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

theorem ngon_sum_char_burnside (n : ℕ) [NeZero n] :
    ∑ g : DihedralGroup n, ngonChar n g =
      Fintype.card (Quotient (MulAction.orbitRel (DihedralGroup n) (ZMod n))) *
        Fintype.card (DihedralGroup n) :=
  MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (DihedralGroup n) (ZMod n)

/-- The linear character of `DihedralGroup n` that is `1` on rotations and `-1` on reflections. -/
