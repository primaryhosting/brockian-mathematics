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

theorem hasDensityZero_squares : HasDensityZero {n : ℕ | IsSquare n} := by
  refine hasDensityZero_of_eventually_le (fun ε hε => ?_)
  obtain ⟨k, hk⟩ := exists_nat_gt (2 / ε)
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      have : (0 : ℝ) < 2 / ε := by positivity
      simp only [Nat.cast_zero] at hk
      linarith
    · exact h
  refine ⟨(k + 1) * (k + 1), fun x hx => ?_⟩
  have hxk : k ≤ Nat.sqrt x := by
    have hkk : k * k ≤ x := by nlinarith
    exact Nat.le_sqrt.2 hkk
  have hsq : Nat.sqrt x * Nat.sqrt x ≤ x := by
    have := Nat.sqrt_le' x
    nlinarith [this, sq (Nat.sqrt x)]
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hxpos : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have key : (k : ℝ) * ((Nat.sqrt x : ℝ) + 1) ≤ 2 * x := by
    have h1 : k * (Nat.sqrt x + 1) ≤ 2 * x := by
      have hmul : k * Nat.sqrt x ≤ Nat.sqrt x * Nat.sqrt x := Nat.mul_le_mul_right _ hxk
      have hk1 : k ≤ x := le_trans hxk (Nat.sqrt_le_self x)
      nlinarith
    exact_mod_cast h1
  have hεk : 2 / (k : ℝ) ≤ ε := by
    rw [div_le_iff₀ hkR]
    rw [div_lt_iff₀ hε] at hk
    nlinarith
  have h1 : (count {n : ℕ | IsSquare n} x : ℝ) ≤ (Nat.sqrt x : ℝ) + 1 := by
    have := count_squares_le x
    have : (count {n : ℕ | IsSquare n} x : ℝ) ≤ ((Nat.sqrt x + 1 : ℕ) : ℝ) := by
      exact_mod_cast this
    simpa using this
  have hstep : (Nat.sqrt x : ℝ) + 1 ≤ (2 / (k : ℝ)) * x := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hkR]
    nlinarith [key]
  calc (count {n : ℕ | IsSquare n} x : ℝ) ≤ (Nat.sqrt x : ℝ) + 1 := h1
    _ ≤ (2 / (k : ℝ)) * x := hstep
    _ ≤ ε * x := mul_le_mul_of_nonneg_right hεk hxpos

/-! ## Structure of betrothed numbers -/

