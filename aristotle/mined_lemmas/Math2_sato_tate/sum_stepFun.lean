/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Topology Set MeasureTheory intervalIntegral
open scoped Real

namespace Math2

/-- The Sato–Tate density on `[0, π]`: `θ ↦ (2/π) sin²θ`. -/

lemma sum_stepFun (f : ℝ → ℝ) (n : ℕ) {θ : ℕ → ℝ} (hrange : ∀ p, θ p ∈ Icc 0 Real.pi) (X : ℕ) :
    (∑ p ∈ primesBelow X, stepFun f n (θ p))
      = ((primesBelow X).card : ℝ) * f Real.pi
        + ∑ j ∈ Finset.range n, (f (grid n j) - f (grid n (j + 1))) *
            ((((primesBelow X).filter fun p => θ p ∈ Icc 0 (grid n j)).card : ℝ)) := by
  unfold stepFun
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum, Finset.card_filter]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  have hp := hrange p
  by_cases h : θ p ≤ grid n j
  · simp [h, mem_Icc, hp.1]
  · simp [h, mem_Icc]


