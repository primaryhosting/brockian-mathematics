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

lemma integral_empirical (θ : ℕ → ℝ) (f : ℝ → ℝ) {X : ℕ} (hX : (Nat.primesBelow X).card ≠ 0) :
    ∫ t, f t ∂(empirical θ X) = primeAverage θ f X := by
  rw [empirical, if_neg hX, integral_smul_measure,
    integral_finset_sum_measure fun i _ => integrable_dirac (by simp)]
  simp only [integral_dirac, primeAverage]
  rw [ENNReal.toReal_inv, smul_eq_mul, div_eq_inv_mul]
  simp

