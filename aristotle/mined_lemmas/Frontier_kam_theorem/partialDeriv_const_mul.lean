import Mathlib

/-!
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
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

namespace Frontier

variable {n : ℕ}

/-- Pairing of an integer covector `k` with a real vector `x`: `⟪k, x⟫ = ∑ i, k i * x i`. -/

lemma partialDeriv_const_mul (f : (Fin n → ℝ) → ℝ) (c : ℝ) (j : Fin n) (x : Fin n → ℝ) :
    partialDeriv (fun y => c * f y) j x = c * partialDeriv f j x := by
  simp only [partialDeriv]
  exact deriv_const_mul_field c

