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

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal NNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

open MeasureTheory Filter Topology Set

/-- The Sato–Tate density on `[0, π]`: `θ ↦ (2/π) sin²θ`. -/

lemma empirical_apply (θ : ℕ → ℝ) {X : ℕ} (hX : (Nat.primesBelow X).card ≠ 0)
    {s : Set ℝ} (hs : MeasurableSet s) :
    empirical θ X s = ((Nat.primesBelow X).card : ℝ≥0∞)⁻¹ *
      (((Nat.primesBelow X).filter fun p => θ p ∈ s).card : ℝ≥0∞) := by
  rw [empirical, if_neg hX, Measure.smul_apply, Measure.coe_finset_sum]
  simp only [Finset.sum_apply, MeasureTheory.Measure.dirac_apply' _ hs, smul_eq_mul]
  congr 1
  rw [Finset.sum_indicator_eq_sum_filter]
  simp

instance (θ : ℕ → ℝ) (X : ℕ) : IsProbabilityMeasure (empirical θ X) := by
  by_cases hX : (Nat.primesBelow X).card = 0
  · rw [empirical, if_pos hX]; infer_instance
  · constructor
    rw [empirical_apply θ hX MeasurableSet.univ]
    simp only [Set.mem_univ, Finset.filter_true_of_mem, implies_true]
    exact ENNReal.inv_mul_cancel (by simpa using hX) (by simp)

/-- The empirical distributions as probability measures. -/
