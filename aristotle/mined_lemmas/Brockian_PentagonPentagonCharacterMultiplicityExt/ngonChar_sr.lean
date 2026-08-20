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

lemma ngonChar_sr (n : ℕ) [NeZero n] (i : ZMod n) :
    ngonChar n (DihedralGroup.sr i) = (Finset.univ.filter fun x : ZMod n => 2 * x = i).card := by
  classical
  rw [ngonChar_eq_card_filter]
  congr 1
  ext x
  constructor
  · intro hx
    have hx' : i - x = x := by simpa using hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    linear_combination -hx'
  · intro hx
    have hx' : 2 * x = i := by simpa using hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, sr_smul]
    linear_combination -hx'

/-- Splitting a sum over the dihedral group into its rotation and reflection parts. -/
