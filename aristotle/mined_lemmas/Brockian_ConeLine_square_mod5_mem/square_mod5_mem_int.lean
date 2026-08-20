/-
# Square Mod 5 Mem
Category: Cone Line
Target: Brockian.ConeLine.square_mod5_mem
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian.ConeLine

/-- Perfect squares land only on rays `0`, `1`, `4` modulo `5`. -/

theorem square_mod5_mem_int :
    ∀ n : ℤ, ((n ^ 2 : ℤ) : ZMod 5) = 0 ∨ ((n ^ 2 : ℤ) : ZMod 5) = 1 ∨
      ((n ^ 2 : ℤ) : ZMod 5) = 4 := by
  intro n
  have h : ((n : ZMod 5)) ^ 2 = 0 ∨ ((n : ZMod 5)) ^ 2 = 1 ∨ ((n : ZMod 5)) ^ 2 = 4 :=
    square_mod5_mem (n : ZMod 5)
  simpa using h

/-- The `Int.emod` form: `n ^ 2 % 5 ∈ ({0, 1, 4} : Set ℤ)`. -/
