/-
# Ray Indicator Eq Char Sum
Category: Characters
Target: Brockian.Characters5.rayIndicator_eq_charSum
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

set_option grind.warning false

namespace Brockian
namespace Characters5

/-- The primitive fifth root of unity `ω = exp(2πi/5)`. -/

lemma omega_ne_one : ω ≠ 1 := by
  rw [omega]
  intro hEq
  rw [Complex.exp_eq_one_iff] at hEq
  obtain ⟨n, hn⟩ := hEq
  have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h : ((1 : ℂ) / 5) * (2 * (Real.pi : ℂ) * Complex.I)
      = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    linear_combination hn
  have hn5 : (n : ℂ) = 1 / 5 := (mul_right_cancel₀ hc h).symm
  have h2 : ((5 * n : ℤ) : ℂ) = ((1 : ℤ) : ℂ) := by push_cast [hn5]; ring
  have h3 := (Int.cast_injective (α := ℂ)) h2
  omega

