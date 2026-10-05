import Mathlib

/-!
# Norm E
Category: Characters
Target: Brockian.Characters5.norm_e
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity, `ω = exp(2πi/5)`. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character on `ZMod 5`, `e k = ω ^ k`. -/
noncomputable def e (k : ZMod 5) : ℂ := ω ^ (k.val)

theorem norm_omega : ‖ω‖ = 1 := by
  have h : (2 * (Real.pi : ℂ) * Complex.I / 5) = ((2 * Real.pi / 5 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [ω, h, Complex.norm_exp_ofReal_mul_I]

theorem norm_e (k : ZMod 5) : ‖e k‖ = 1 := by
  rw [e, norm_pow, norm_omega, one_pow]

end Characters5
end Brockian

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

