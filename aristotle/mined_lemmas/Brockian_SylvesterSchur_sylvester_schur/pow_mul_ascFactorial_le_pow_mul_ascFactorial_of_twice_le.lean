import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma pow_mul_ascFactorial_le_pow_mul_ascFactorial_of_twice_le
    {n i : ℕ} (htwice : 2 * i ≤ n) :
    n ^ i * (i + 1).ascFactorial i ≤
      (2 * i) ^ i * (n - i + 1).ascFactorial i := by
  rw [Nat.ascFactorial_eq_prod_range, Nat.ascFactorial_eq_prod_range]
  calc
    n ^ i * (∏ t ∈ Finset.range i, (i + 1 + t))
        = (∏ _t ∈ Finset.range i, n) *
            ∏ t ∈ Finset.range i, (i + 1 + t) := by
          rw [Finset.prod_const, Finset.card_range]
    _ = ∏ t ∈ Finset.range i, (n * (i + 1 + t)) := by
          rw [Finset.prod_mul_distrib]
    _ ≤ ∏ t ∈ Finset.range i, ((2 * i) * (n - i + 1 + t)) := by
          refine Finset.prod_le_prod' ?_
          intro t ht
          rw [Finset.mem_range] at ht
          have hni : i ≤ n := by omega
          zify [hni] at *
          nlinarith [htwice, ht]
    _ = (∏ _t ∈ Finset.range i, (2 * i)) *
          ∏ t ∈ Finset.range i, (n - i + 1 + t) := by
          rw [Finset.prod_mul_distrib]
    _ = (2 * i) ^ i * ∏ t ∈ Finset.range i, (n - i + 1 + t) := by
          rw [Finset.prod_const, Finset.card_range]

