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

lemma integral_cos_nat_mul {k : ℕ} (hk : 1 ≤ k) : ∫ t in (0:ℝ)..π, Real.cos (k * t) = 0 := by
  have hk0 : (k:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hk0]
  simp [Real.sin_nat_mul_pi]

