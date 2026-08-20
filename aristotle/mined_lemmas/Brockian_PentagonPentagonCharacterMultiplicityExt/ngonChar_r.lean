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

lemma ngonChar_r (n : ℕ) [NeZero n] (i : ZMod n) :
    ngonChar n (DihedralGroup.r i) = if i = 0 then n else 0 := by
  classical
  rw [ngonChar_eq_card_filter]
  by_cases h : i = 0
  · simp [h, ZMod.card]
  · simp [sub_eq_self, h]

/-- The character value at a reflection: the fixed vertices of `sr i` are the solutions of
`2 * x = i`. -/
