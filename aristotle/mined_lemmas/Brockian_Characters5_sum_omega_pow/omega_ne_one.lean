import Mathlib

/-!
# Sum Omega Pow
Category: Characters
Target: Brockian.Characters5.sum_omega_pow
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

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/

theorem omega_ne_one : ω ≠ 1 := by
  intro h
  have := isPrimitiveRoot_omega.eq_orderOf
  rw [h] at this
  simp at this

