import Mathlib

/-!
# Omega Pow Five
Category: Characters
Target: Brockian.Characters5.omega_pow_five
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.Characters5

open Complex

/-- The Brockian ray rotation: `ω = e^{2πi/5}`. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- Key intermediate lemma: `ω` is a primitive 5-th root of unity. -/
theorem isPrimitiveRoot_omega : IsPrimitiveRoot ω 5 := by
  have h := Complex.isPrimitiveRoot_exp 5 (by norm_num)
  have hω : ω = Complex.exp (2 * Real.pi * Complex.I / (5 : ℕ)) := by
    norm_num [ω]
  rw [hω]
  exact h

/-- The Brockian ray rotation returns to start after five steps: `ω ^ 5 = 1`. -/
theorem omega_pow_five : ω ^ 5 = 1 := isPrimitiveRoot_omega.pow_eq_one

end Brockian.Characters5

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

