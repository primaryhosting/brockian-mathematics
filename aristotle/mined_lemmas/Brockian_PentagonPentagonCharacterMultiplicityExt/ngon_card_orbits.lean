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

lemma ngon_card_orbits (n : ℕ) [NeZero n] :
    Fintype.card (Quotient (MulAction.orbitRel (DihedralGroup n) (ZMod n))) = 1 := by
  refine Fintype.card_eq_one_iff.mpr ⟨Quotient.mk _ 0, ?_⟩
  refine Quotient.ind ?_
  intro a
  refine Quotient.sound ?_
  show (MulAction.orbitRel (DihedralGroup n) (ZMod n)) a 0
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  exact ⟨DihedralGroup.r (-a), by show (0 : ZMod n) - (-a) = a; ring⟩

/-- The permutation character of the `n`-gon vertex action: `χ g` is the number of vertices
fixed by `g`. -/
