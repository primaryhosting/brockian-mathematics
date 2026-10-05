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

lemma stIntegral_sub {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    stIntegral (fun t => f t - g t) = stIntegral f - stIntegral g := by
  unfold stIntegral
  simp only [sub_mul]
  exact intervalIntegral.integral_sub ((hf.mul continuous_stDensity).intervalIntegrable _ _)
    ((hg.mul continuous_stDensity).intervalIntegrable _ _)

