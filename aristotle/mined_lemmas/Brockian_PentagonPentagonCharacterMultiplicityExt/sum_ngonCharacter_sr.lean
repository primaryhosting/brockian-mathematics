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

lemma sum_ngonCharacter_sr (n : ℕ) [NeZero n] :
    ∑ i : ZMod n, ngonCharacter n (DihedralGroup.sr i) = n := by
  classical
  have key : (Finset.univ : Finset (ZMod n)).card =
      ∑ i ∈ (Finset.univ : Finset (ZMod n)),
        (Finset.univ.filter (fun v : ZMod n => v + v = i)).card :=
    Finset.card_eq_sum_card_fiberwise (fun v _ => Finset.mem_univ (v + v))
  have hchar : ∀ i : ZMod n, ngonCharacter n (DihedralGroup.sr i) =
      (Finset.univ.filter (fun v : ZMod n => v + v = i)).card := by
    intro i
    unfold ngonCharacter
    congr 1
    apply Finset.filter_congr
    intro v _
    simp only [ngonPerm_sr]
    constructor
    · intro h; linear_combination -h
    · intro h; linear_combination -h
  calc ∑ i : ZMod n, ngonCharacter n (DihedralGroup.sr i)
      = ∑ i : ZMod n, (Finset.univ.filter (fun v : ZMod n => v + v = i)).card := by
        exact Finset.sum_congr rfl (fun i _ => hchar i)
    _ = (Finset.univ : Finset (ZMod n)).card := key.symm
    _ = n := by simp [ZMod.card]

/-- The dihedral group `D n` as a disjoint union of rotations and reflections. -/
