import Mathlib
/-!
# Hwin Nonneg Iff Threshold
Category: A Assembly
Target: Zeta23Scaffold.Hwin_nonneg_iff_threshold
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

namespace Zeta23Scaffold

/-- The "window" function `H(λ) = 2 - 1/λ - λ/3`. -/

theorem sqrt_six_bounds : 2 < Real.sqrt 6 ∧ Real.sqrt 6 < 3 := by
  constructor
  · have : (2 : ℝ) = Real.sqrt 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    rw [this]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  · have : (3 : ℝ) = Real.sqrt 9 := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3)]
    rw [this]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- `H(λ) ≥ 0` iff `λ ≥ 3 - √6 ≈ 0.5505…`, on the range `0 < λ ≤ 1`. -/
