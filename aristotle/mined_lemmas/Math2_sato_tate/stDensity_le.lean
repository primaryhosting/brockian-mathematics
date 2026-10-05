import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
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

namespace Math2

open Filter Topology Set Polynomial

/-- The Sato–Tate density `(2/π) sin²θ` on the interval `[0, π]`. -/

lemma stDensity_le (t : ℝ) : stDensity t ≤ 2 / π := by
  unfold stDensity
  have h1 : Real.sin t ^ 2 ≤ 1 := by
    rw [sq]; nlinarith [Real.neg_one_le_sin t, Real.sin_le_one t]
  have h2 : (0:ℝ) < 2 / π := by positivity
  nlinarith

