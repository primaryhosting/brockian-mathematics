import Mathlib

/-!
# Wigderson Expander Mixing
Category: Frontier Abel
Target: Frontier.wigderson_expander_mixing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace Frontier

section Aux

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- Cauchy–Schwarz for finite sums, in absolute-value / square-root form. -/

lemma abs_sum_mul_le_sqrt_mul_sqrt (u v : V → ℝ) :
    |∑ i, u i * v i| ≤ Real.sqrt (∑ i, (u i) ^ 2) * Real.sqrt (∑ i, (v i) ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
  have h0 : (0:ℝ) ≤ ∑ i, (u i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul h0]
  exact Real.sqrt_le_sqrt h

/-- Summing against the indicator vector of a finset restricts the sum to that finset. -/
