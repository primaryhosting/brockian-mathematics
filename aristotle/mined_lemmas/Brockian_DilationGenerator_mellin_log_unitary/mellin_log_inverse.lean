import Mathlib

/-!
# Mellin Log Unitary
Category: Gate1 Operator
Target: Brockian.DilationGenerator.mellin_log_unitary
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

namespace DilationGenerator

open MeasureTheory Set

/-- The substitution `x = exp t` maps `ℝ` bijectively onto `(0, ∞)`. -/

theorem mellin_log_inverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) {x : ℝ} (hx : 0 < x) :
    (x ^ (-(1 : ℝ) / 2) * Real.exp (Real.log x / 2)) • f (Real.exp (Real.log x)) = f x := by
  rw [Real.exp_log hx]
  have h1 : Real.exp (Real.log x / 2) = x ^ ((1 : ℝ) / 2) := by
    rw [Real.rpow_def_of_pos hx]
    ring_nf
  rw [h1, ← Real.rpow_add hx]
  norm_num

end DilationGenerator

end Brockian

