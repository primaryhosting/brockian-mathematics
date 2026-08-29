import Mathlib

/-!
# Deutsch Correct
Category: Quantum Computing
Target: QC.deutsch_correct
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

namespace QC

/-- A two–qubit state is an amplitude vector indexed by `Bool × Bool`. -/
abbrev State := Bool × Bool → ℂ

/-- `1/√2`, the normalisation constant of the Hadamard gate. -/

theorem deutschState_normalized (f : Bool → Bool) :
    ∑ p : Bool × Bool, ‖deutschState f p‖ ^ 2 = 1 := by
  have h0 := deutschState_false f false
  have h1 := deutschState_false f true
  have h2 := deutschState_true f false
  have h3 := deutschState_true f true
  cases hf : f false <;> cases ht : f true <;>
    simp only [hf, ht, sgn, if_true] at h0 h1 h2 h3 <;>
    norm_num [Fintype.sum_prod_type, h0, h1, h2, h3, norm_mul, mul_pow, norm_isqrt2_sq]

end QC

