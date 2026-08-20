import Mathlib
namespace Brockian.OddPerfectThreePrimes

open Finset

/-- For a prime `p`, `(p-1) * σ₁(p^a) = p^(a+1) - 1 < p * p^a`. -/

private lemma sigma_primePow_bound {p : ℕ} (hp : p.Prime) (a : ℕ) :
    (p - 1) * (∑ d ∈ (p ^ a).divisors, d) < p * p ^ a := by
  have hdiv : (p ^ a).divisors = Finset.image (fun i => p ^ i) (Finset.range (a + 1)) := by
    ext x
    simp [Nat.divisors_prime_pow hp]
  rw [hdiv]
  rw [Finset.sum_image]
  · have hp1 : 1 < p := hp.one_lt
    have hsum : (p - 1) * (∑ x ∈ Finset.range (a + 1), p ^ x) = p ^ (a + 1) - 1 := by
      induction a + 1 with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, pow_succ]
        rw [mul_add, ih]
        have h1 : p ^ n - 1 + (p - 1) * p ^ n = p ^ n * p - 1 := by
          have h2 : (p - 1) * p ^ n + p ^ n = p * p ^ n := by
            have := Nat.sub_add_cancel hp.one_lt.le
            calc (p - 1) * p ^ n + p ^ n = ((p - 1) + 1) * p ^ n := by ring
              _ = p * p ^ n := by rw [this]
          calc p ^ n - 1 + (p - 1) * p ^ n
                = (p - 1) * p ^ n + (p ^ n - 1) := by ring
            _ = (p - 1) * p ^ n + p ^ n - 1 := by rw [Nat.add_sub_assoc (Nat.one_le_pow n p hp.pos)]
            _ = p * p ^ n - 1 := by rw [h2]
            _ = p ^ n * p - 1 := by rw [mul_comm]
        exact h1
    rw [hsum]
    rw [pow_succ]
    rw [mul_comm]
    exact Nat.sub_lt (mul_pos hp.pos (pow_pos hp.pos _)) zero_lt_one
  · intro i hi j hj h
    exact Nat.pow_right_injective hp.one_lt h

/-- The sum-of-divisors function is multiplicative over a finite family of pairwise coprime,
nonzero numbers. -/
