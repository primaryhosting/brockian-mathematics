/-
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Statement: Yao's minimax principle relates randomized and distributional complexity.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Statement: Yao's minimax principle relates randomized and distributional complexity.
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

variable {A I : Type*} [Fintype A] [Nonempty A] [Fintype I] [Nonempty I]

/-- The expected cost of the randomized algorithm given by the mixed strategy `p`
(a distribution over the deterministic algorithms `A`) on the worst-case input. -/

lemma abs_expect_le' (C : A → I → ℝ) {q : I → ℝ} (hq : q ∈ stdSimplex ℝ I) (a : A) :
    |∑ i, q i * C a i| ≤ costBound C := by
  obtain ⟨hq0, hq1⟩ := hq
  calc |∑ i, q i * C a i| ≤ ∑ i, |q i * C a i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, q i * costBound C := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul, abs_of_nonneg (hq0 i)]
        exact mul_le_mul_of_nonneg_left (le_costBound C a i) (hq0 i)
    _ = costBound C := by rw [← Finset.sum_mul, hq1, one_mul]

