/-!
# Ackermann Total
Category: Computer Science
Target: CS.ackermann_total
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- The lexicographic order on `Nat × Nat`, used as the termination measure for the Ackermann
recursion. -/

theorem ackermann_total_existsUnique (m n : ℕ) : ∃! v : ℕ, AckGraph m n v :=
  ⟨_root_.ack m n, ackGraph_mathlib_ack m n,
    fun _ h => (eq_ack_of_ackGraph h).trans (cs_ack_eq_ack m n)⟩

/-- Sanity check: the value determined by the recursion at `(2, 5)` is `13`. -/
example : ∃! v : ℕ, AckGraph 2 5 v := by
  refine ⟨13, ?_, fun w hw => ?_⟩
  · have : (13 : ℕ) = _root_.ack 2 5 := by simp
    rw [this]
    exact ackGraph_mathlib_ack 2 5
  · rw [eq_ack_of_ackGraph hw, cs_ack_eq_ack]
    simp

end CS

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

