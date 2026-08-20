import Mathlib
open Finset
namespace MS2.Combinatorics2

/-- Segner's recurrence for the Catalan numbers, stated as a sum over `range (n+1)`. -/

theorem derangement_formula' (n : ℕ) :
    (numDerangements n : ℚ)
      = (Nat.factorial n : ℚ) * ∑ k ∈ range (n+1), (-1:ℚ)^k / (Nat.factorial k : ℚ) := by
  have h := numDerangements_sum n
  have h2 : (numDerangements n : ℚ)
      = ∑ k ∈ range (n + 1), (-1 : ℚ) ^ k * Nat.ascFactorial (k + 1) (n - k) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) h
  rw [h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_range, Nat.lt_succ_iff] at hk
  have hf : (Nat.factorial k) * Nat.ascFactorial (k+1) (n - k) = Nat.factorial n := by
    rw [Nat.factorial_mul_ascFactorial]
    congr 1
    omega
  have hk0 : (Nat.factorial k : ℚ) ≠ 0 := by positivity
  field_simp
  rw [← hf]
  push_cast
  ring

/-- The binomial theorem over `ℝ`. -/
