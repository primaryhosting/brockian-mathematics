/-
# Omega Pow Five
Category: Characters
Target: Brockian.Characters5.omega_pow_five
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Omega Pow Five
Category: Characters
Target: Brockian.Characters5.omega_pow_five
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

namespace Brockian
namespace Characters5

/-- The Brockian ray rotation: the primitive fifth root of unity `ω = e^{2πi/5}`. -/

theorem isPrimitiveRoot_omega : IsPrimitiveRoot ω 5 := by
  have h := Complex.isPrimitiveRoot_exp 5 (by norm_num)
  have hcast : (2 * (Real.pi : ℂ) * Complex.I / ((5 : ℕ) : ℂ))
      = 2 * (Real.pi : ℂ) * Complex.I / 5 := by
    norm_num
  rw [hcast] at h
  exact h

/-- The Brockian ray rotation returns to start after five steps: `ω ^ 5 = 1`. -/
