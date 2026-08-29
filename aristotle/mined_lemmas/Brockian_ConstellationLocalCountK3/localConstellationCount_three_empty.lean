/-
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
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

/-- The *local constellation count* of a set `S ⊆ ℕ` with respect to a pattern
`h : Fin k → ℕ` in the window `[0, N)`: the number of `n < N` such that the whole
translated constellation `n + h 0, …, n + h (k-1)` lies inside `S`. -/

theorem localConstellationCount_three_empty (a b c N : ℕ) :
    localConstellationCount (∅ : Set ℕ) ![a, b, c] N = 0 := by
  rw [localConstellationCount_three]
  simp

end Brockian

