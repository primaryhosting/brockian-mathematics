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

lemma dotIR_update (k : Fin n → ℤ) (θ : Fin n → ℝ) (j : Fin n) (s : ℝ) :
    dotIR k (Function.update θ j s) =
      (k j : ℝ) * s + ∑ i ∈ Finset.univ.erase j, (k i : ℝ) * θ i := by
  simp only [dotIR]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  rw [Function.update_self, add_comm]
  congr 1
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

