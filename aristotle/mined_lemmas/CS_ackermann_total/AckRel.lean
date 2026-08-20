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

theorem AckRel.functional {m n v w : ℕ} (h1 : AckRel m n v) (h2 : AckRel m n w) : v = w := by
  induction h1 generalizing w with
  | zero n => cases h2; rfl
  | succZero _ ih => cases h2 with | succZero h' => exact ih h'
  | succSucc _ _ ih1 ih2 =>
    cases h2 with
    | succSucc k1 k2 =>
      have hr := ih1 k1
      subst hr
      exact ih2 k2

/-- The defined function `ack` satisfies the Ackermann equations. -/
