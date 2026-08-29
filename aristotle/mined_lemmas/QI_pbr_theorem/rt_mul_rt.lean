/-
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open MeasureTheory MeasureTheory.Measure Complex

noncomputable section

/-! ## The quantum input: the Pusey–Barrett–Rudolph measurement on two qubits -/

/-- The real number `1/√2`, viewed as a complex amplitude. -/

lemma rt_mul_rt : rt * rt = 1 / 2 := by
  have h : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) h
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    intro h0
    rw [h0] at h2
    norm_num at h2
  simp only [rt, Complex.ofReal_inv]
  field_simp
  linear_combination -h2

