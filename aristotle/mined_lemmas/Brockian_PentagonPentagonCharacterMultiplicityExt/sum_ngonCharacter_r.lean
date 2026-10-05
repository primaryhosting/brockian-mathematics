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

/-- The permutation representation of the dihedral group `D n` on the `n` vertices of a
regular `n`-gon (vertices modelled by `ZMod n`): the rotation `r i` sends a vertex `v` to
`v - i`, and the reflection `sr i` sends `v` to `i - v`. -/

lemma sum_ngonCharacter_r (n : ℕ) [NeZero n] :
    ∑ i : ZMod n, ngonCharacter n (DihedralGroup.r i) = n := by
  classical
  have h0 : ngonCharacter n (DihedralGroup.r 0) = n := by
    unfold ngonCharacter
    simp [ZMod.card]
  rw [Finset.sum_eq_single (0 : ZMod n) ?_ ?_]
  · exact h0
  · intro i _ hi
    unfold ngonCharacter
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro v _
    simp only [ngonPerm_r]
    intro h
    exact hi (by linear_combination -h)
  · intro h
    exact absurd (Finset.mem_univ (0 : ZMod n)) h

/-- The reflections of the `n`-gon contribute `n` fixed vertices in total. -/
