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

import Mathlib
import RequestProject.TwoSquares53

/-!
# Two Squares 53, Mathlib restatement

`Math.two_squares_53` states primality of `53` elementarily (no imports are allowed in that file,
because the mandated header comment must come first).  Here we check that the elementary
statement is equivalent to `Nat.Prime 53`, and restate the theorem in Mathlib terms.
-/

namespace Math

/-- The elementary primality condition used in `Math.two_squares_53` indeed gives `Nat.Prime 53`. -/

theorem prime_53_of_two_squares_53 : Nat.Prime 53 := by
  have h := two_squares_53.1
  rw [Nat.prime_def_lt]
  exact ⟨h.1, fun m hm hdvd => h.2 m hm hdvd⟩

/-- **The prime 53 is a sum of two squares**, in Mathlib terms. -/
