import Mathlib

/-!
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

open scoped BigOperators
open scoped Classical
open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian
namespace BetrothedNumbers

/-! ## Betrothed (quasi-amicable) numbers -/

/-- `n` and `m` form a *betrothed* (quasi-amicable) pair: they are distinct positive
integers whose sums of divisors both equal `n + m + 1`, i.e. each is the sum of the
proper divisors, excluding `1`, of the other. -/

theorem hasDensityZero_of_eventually_le {A : Set ℕ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ x ≥ N, (count A x : ℝ) ≤ ε * x) :
    HasDensityZero A := by
  rw [HasDensityZero, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := h (ε / 2) (by linarith)
  refine ⟨max N 1, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_right N 1) hx
  have hxN : N ≤ x := le_trans (le_max_left N 1) hx
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx1
  have h1 : (count A x : ℝ) ≤ (ε / 2) * x := hN x hxN
  have h0 : (0 : ℝ) ≤ (count A x : ℝ) / x := div_nonneg (by positivity) (le_of_lt hxpos)
  have h2 : (count A x : ℝ) / x ≤ ε / 2 := by rw [div_le_iff₀ hxpos]; exact h1
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  linarith

/-- The converse criterion: density zero gives eventual bounds `count A x ≤ ε x`. -/
