/-
# Hwin Nonneg Iff Threshold
Category: A Assembly
Target: Zeta23Scaffold.Hwin_nonneg_iff_threshold
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Zeta23Scaffold

/-- The "window" function `H(λ) = 2 - 1/λ - λ/3`. -/

lemma sqrt_six_lt_three : Real.sqrt 6 < 3 := by
  have h : Real.sqrt 6 < Real.sqrt 9 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h9 : Real.sqrt 9 = 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  linarith [h, h9.le, h9.symm.le]

/-- On `0 < λ ≤ 1`, `H(λ) ≥ 0` iff `λ ≥ 3 - √6 ≈ 0.5505`. -/
