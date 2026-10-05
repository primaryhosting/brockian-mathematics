/-
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to come before any module docstring, so the required header appears
-- at the top of the file as a plain comment and again here as the module docstring.)

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

variable {A I : Type*} [Fintype A] [Fintype I] [Nonempty A] [Nonempty I]

/-- The worst-case expected cost of the randomized algorithm given by the distribution `p`
over deterministic algorithms:  `max over inputs i of  E_{a ~ p} [c a i]`. -/

theorem distCost_le_randCost {c : A → I → ℝ} {p : A → ℝ} {q : I → ℝ}
    (hp : p ∈ stdSimplex ℝ A) (hq : q ∈ stdSimplex ℝ I) :
    distCost c q ≤ randCost c p := by
  have key : ∑ a, p a * (∑ i, q i * c a i) = ∑ i, q i * (∑ a, p a * c a i) := by
    have e1 : ∀ a : A, p a * (∑ i, q i * c a i) = ∑ i, p a * q i * c a i := by
      intro a; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    have e2 : ∀ i : I, q i * (∑ a, p a * c a i) = ∑ a, p a * q i * c a i := by
      intro i; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
    rw [Finset.sum_congr rfl fun a _ => e1 a, Finset.sum_congr rfl fun i _ => e2 i]
    exact Finset.sum_comm
  have h1 : distCost c q = ∑ a, p a * distCost c q := by
    rw [← Finset.sum_mul, hp.2, one_mul]
  have h2 : ∑ a, p a * distCost c q ≤ ∑ a, p a * (∑ i, q i * c a i) :=
    Finset.sum_le_sum fun a _ => by
      exact mul_le_mul_of_nonneg_left (distCost_le c q a) (hp.1 a)
  have h3 : ∑ i, q i * (∑ a, p a * c a i) ≤ ∑ i, q i * randCost c p :=
    Finset.sum_le_sum fun i _ => by
      exact mul_le_mul_of_nonneg_left (le_randCost c p i) (hq.1 i)
  have h4 : ∑ i, q i * randCost c p = randCost c p := by
    rw [← Finset.sum_mul, hq.2, one_mul]
  calc distCost c q = ∑ a, p a * distCost c q := h1
    _ ≤ ∑ a, p a * (∑ i, q i * c a i) := h2
    _ = ∑ i, q i * (∑ a, p a * c a i) := key
    _ ≤ ∑ i, q i * randCost c p := h3
    _ = randCost c p := h4

/-! ### The separation argument (the "hard" direction) -/

/-- The linear map sending a distribution over algorithms to its vector of expected costs. -/
