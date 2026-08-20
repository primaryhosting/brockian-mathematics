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

lemma dotIR_add_smul (k : Fin n → ℤ) (θ ω : Fin n → ℝ) (t : ℝ) :
    dotIR k (θ + t • ω) = dotIR k θ + t * dotIR k ω := by
  simp only [dotIR, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

