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

/-- Pigeonhole: among five Booleans, three are equal. -/

private lemma pigeon_five (f : Fin 5 → Bool) :
    ∃ a b d : Fin 5, a ≠ b ∧ a ≠ d ∧ b ≠ d ∧ f a = f b ∧ f a = f d := by
  revert f
  decide

/-- The pentagon colouring of `K₅`: an edge is `true` iff its endpoints are
consecutive modulo `5`. -/
