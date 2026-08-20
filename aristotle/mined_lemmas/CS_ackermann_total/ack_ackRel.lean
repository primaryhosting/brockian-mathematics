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

namespace CS

/-- The Ackermann function, defined by well-founded recursion on the
lexicographic order on `ℕ × ℕ`. -/

theorem ack_ackRel : ∀ m n : ℕ, AckRel m n (ack m n)
  | 0, n => by simpa using AckRel.zero n
  | m + 1, 0 => by simpa using AckRel.succZero (ack_ackRel m 1)
  | m + 1, n + 1 => by
    simpa using AckRel.succSucc (ack_ackRel (m + 1) n) (ack_ackRel m (ack (m + 1) n))
termination_by m n => (m, n)

/-- **The Ackermann function is total.**  For every pair `(m, n)` of natural numbers there is a
unique value satisfying the Ackermann recursion equations; it is computed by `CS.ack`, which is
defined by well-founded recursion on the lexicographic order on `ℕ × ℕ`. -/
