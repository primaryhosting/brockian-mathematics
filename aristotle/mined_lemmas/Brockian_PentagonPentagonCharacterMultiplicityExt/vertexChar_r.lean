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

theorem vertexChar_r (n : ℕ) [NeZero n] (i : ZMod n) :
    vertexChar n (.r i) = if i = 0 then (n : ℂ) else 0 := by
  have h : ∀ x : ZMod n, (vertexPerm n (.r i) x = x) ↔ i = 0 := by
    intro x
    simp [sub_eq_self]
  simp only [vertexChar, h]
  by_cases hi : i = 0 <;> simp [hi, ZMod.card]

/-- The value of the vertex character at the identity is the number of vertices. -/
