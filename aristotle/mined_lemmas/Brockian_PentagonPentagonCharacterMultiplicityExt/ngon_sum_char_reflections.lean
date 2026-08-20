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

lemma ngon_sum_char_reflections (n : ℕ) [NeZero n] :
    ∑ i : ZMod n, ngonChar n (DihedralGroup.sr i) = n := by
  classical
  have h : ∀ i : ZMod n, ngonChar n (DihedralGroup.sr i)
      = ∑ x : ZMod n, if 2 * x = i then 1 else 0 := by
    intro i
    rw [ngonChar_sr, Finset.card_filter]
  simp only [h]
  rw [Finset.sum_comm]
  simp [ZMod.card]

/-- A direct, Burnside-free evaluation of the sum of the permutation character values. -/
