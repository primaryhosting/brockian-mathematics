/-
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Dilworth
Category: Pure Mathematics
Target: Math.dilworth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

variable {α : Type*} [PartialOrder α]

/-- The finset of all chains (as finsets) contained in a given finset `t`. -/

def IsAntichainCover (F : Finset (Finset α)) : Prop :=
  (∀ s ∈ F, IsAntichain (· ≤ ·) (s : Set α)) ∧ ∀ x : α, ∃ s ∈ F, x ∈ s

/-- The minimal number of antichains needed to cover the poset `α`. -/
