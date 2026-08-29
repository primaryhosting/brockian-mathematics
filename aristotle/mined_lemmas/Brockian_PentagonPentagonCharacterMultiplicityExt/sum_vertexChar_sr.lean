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

theorem sum_vertexChar_sr (n : ℕ) [NeZero n] :
    ∑ i : ZMod n, vertexChar n (.sr i) = (n : ℂ) := by
  have h : ∀ i x : ZMod n, (vertexPerm n (.sr i) x = x) ↔ i = x + x := by
    intro i x
    constructor
    · intro hx
      have : i - x = x := hx
      linear_combination this
    · intro hx
      show i - x = x
      rw [hx]; ring
  simp only [vertexChar, h]
  rw [Finset.sum_comm]
  have : ∀ x : ZMod n, (∑ i : ZMod n, if i = x + x then (1 : ℂ) else 0) = 1 := by
    intro x
    simp
  simp [this, ZMod.card]

/-! ## The two-dimensional characters of the dihedral group -/

/-- A primitive `n`-th root of unity in `ℂ`. -/
