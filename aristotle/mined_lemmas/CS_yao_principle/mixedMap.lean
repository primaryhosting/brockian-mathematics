import Mathlib
/-!
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace CS

variable {A X : Type*} [Fintype A] [Fintype X]

/-- Expected cost of the mixed (randomized) algorithm strategy `q` on the input `x`. -/

noncomputable def mixedMap (cost : A → X → ℝ) : (A → ℝ) →ₗ[ℝ] (X → ℝ) where
  toFun q := mixedCost cost q
  map_add' q r := by
    funext x; simp [mixedCost, add_mul, Finset.sum_add_distrib]
  map_smul' c q := by
    funext x; simp [mixedCost, Finset.mul_sum, mul_assoc]

/-- A point mass is a probability distribution. -/
