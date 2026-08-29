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
# Omega Pow Five
Category: Characters
Target: Brockian.Characters5.omega_pow_five
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace Brockian
namespace Characters5

/-- The Brockian ray rotation `ω = e^{2πi/5}`. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

@[inherit_doc] local notation "ω" => omega

/-- The Brockian ray rotation returns to start after five steps: `ω ^ 5 = 1`. -/
theorem omega_pow_five : ω ^ 5 = 1 := by
  have h : ω ^ 5 = Complex.exp (5 * (2 * Real.pi * Complex.I / 5)) := by
    rw [omega, ← Complex.exp_nat_mul]
    norm_num
  have h5 : (5 : ℂ) * (2 * Real.pi * Complex.I / 5) = 2 * Real.pi * Complex.I := by
    ring
  rw [h, h5, Complex.exp_two_pi_mul_I]

end Characters5
end Brockian

