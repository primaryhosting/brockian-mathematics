import Mathlib

/-!
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
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

namespace QI

open Complex Finset

/-! ## The two-qubit vectors used in the PBR argument -/

/-- The normalisation constant `1/√2`. -/

lemma sqrt2_inv_pow4 : ((Real.sqrt 2)⁻¹ : ℝ) ^ 4 = 1 / 4 := by
  have : ((Real.sqrt 2)⁻¹ : ℝ) ^ 4 = (((Real.sqrt 2)⁻¹ : ℝ) ^ 2) ^ 2 := by ring
  rw [this, sqrt2_inv_sq]; norm_num

