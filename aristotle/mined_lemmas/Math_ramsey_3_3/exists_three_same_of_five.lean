/-
# Ramsey 3 3
Category: Pure Mathematics
Target: Math.ramsey_3_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

namespace Math

/-- A 2-colouring `C` of the edges of the complete graph on `Fin n` has a monochromatic
triangle if there are three distinct vertices all of whose connecting edges receive the
same colour. -/

lemma exists_three_same_of_five (f : Fin 5 → Bool) :
    ∃ i j k : Fin 5, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ f i = f j ∧ f i = f k := by
  revert f
  decide

/-- The colouring of `K₅` given by the 5-cycle: `a` and `b` are joined by a red edge
(`true`) exactly when they are adjacent on the cycle `0-1-2-3-4-0`. -/
