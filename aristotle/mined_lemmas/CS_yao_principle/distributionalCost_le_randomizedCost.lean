import Mathlib

/-!
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
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

namespace CS

section Yao

variable {A I : Type*} [Fintype A] [Fintype I]

/-- The expected cost of the randomized algorithm given by the distribution `p` over
deterministic algorithms, run on the input `i`. -/

theorem distributionalCost_le_randomizedCost [Nonempty A] [Nonempty I] (c : A → I → ℝ)
    {p : A → ℝ} (hp : p ∈ stdSimplex ℝ A) {q : I → ℝ} (hq : q ∈ stdSimplex ℝ I) :
    distributionalCost c q ≤ randomizedCost c p := by
  have h1 : distributionalCost c q ≤ ∑ a, p a * expectedCostOn c q a :=
    inf'_le_weighted hp _
  have h2 : ∑ i, q i * expectedCost c p i ≤ randomizedCost c p :=
    weighted_le_sup' hq _
  have h3 : ∑ a, p a * expectedCostOn c q a = ∑ i, q i * expectedCost c p i := by
    simp only [expectedCost, expectedCostOn, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => by ring
  linarith

