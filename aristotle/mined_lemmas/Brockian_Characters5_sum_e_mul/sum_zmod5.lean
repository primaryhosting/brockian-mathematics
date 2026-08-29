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

/-!
# Sum E Mul
Category: Characters
Target: Brockian.Characters5.sum_e_mul
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Real
open scoped Classical

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/

theorem sum_zmod5 (f : ZMod 5 → ℂ) : ∑ x : ZMod 5, f x = f 0 + f 1 + f 2 + f 3 + f 4 := by
  show ∑ x : Fin 5, f x = _
  rw [Fin.sum_univ_five]

/-- The full character sum vanishes. -/
