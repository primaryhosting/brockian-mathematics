import Mathlib
/-!
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
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

namespace Brockian
namespace BetrothedNumbers

open Filter Finset

/-! ## Natural density -/

/-- The number of elements of `A` in the interval `[1, N]`. -/

lemma sum_one_div_sq_le (N : ℕ) : ∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 2 := by
  rcases Nat.eq_zero_or_pos N with h | h
  · simp [h]
  · have h2 := sum_one_div_sq_le_aux N h
    have h3 : (0:ℝ) < N := by exact_mod_cast h
    have : (0:ℝ) < 1 / N := by positivity
    linarith

/-- The abundancy `σ(n)/n` is the sum of the reciprocals of the divisors of `n`. -/
