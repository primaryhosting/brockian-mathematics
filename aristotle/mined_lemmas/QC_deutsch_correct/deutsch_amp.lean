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

set_option grind.warning false

namespace QC

/-- The sign `(-1)^b` of a bit, as a complex number. -/

theorem deutsch_amp (f : Bool → Bool) (y : Bool) :
    deutsch f (false, y) =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ 3 * sgn y * (sgn (f false) + sgn (f true)) := by
  cases y <;> cases hf : f false <;> cases ht : f true <;>
    simp [deutsch, had₁, had₂, oracle, init, sgn, hf, ht, Prod.ext_iff] <;> ring

/-- If `f` is constant, the algorithm measures `0` on the first qubit with certainty. -/
