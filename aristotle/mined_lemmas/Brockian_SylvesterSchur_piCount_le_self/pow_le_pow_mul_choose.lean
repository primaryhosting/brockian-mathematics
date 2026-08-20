import Mathlib
namespace Brockian.SylvesterSchur

/-!
# The Sylvester–Schur theorem

If `n > k ≥ 1` then one of `n+1, …, n+k` has a prime factor `> k`.

The proof follows Erdős' argument: assuming the contrary, every prime factor of the
binomial coefficient `(n+k).choose k` is at most `k`.  This yields two upper bounds for
that binomial coefficient (one via the number of primes `≤ k`, one via the primorial),
both of which are contradicted by an elementary lower bound, except in a range of small
parameters which is covered by an explicit chain of primes.
-/

open Finset Real

/-! ### An elementary upper bound for the prime counting function -/

/-- The number of primes `≤ k`. -/

theorem pow_le_pow_mul_choose {N k : ℕ} (hkN : k ≤ N) : N ^ k ≤ k ^ k * N.choose k := by
  rcases eq_or_ne k 0 with rfl | hk0
  · simp
  -- Key identity: N.descFactorial k = k! * N.choose k
  have hdesc : N.descFactorial k = k.factorial * N.choose k :=
    Nat.descFactorial_eq_factorial_mul_choose N k
  -- Also: N.descFactorial k = ∏_{i ∈ range k} (N - i)
  have hprod : N.descFactorial k = ∏ i ∈ range k, (N - i) := Nat.descFactorial_eq_prod_range N k
  -- Key: N.choose k = ∏_{i=0}^{k-1} (N-i)/(k-i) ≥ (N/k)^k
  -- So N^k ≤ k^k * N.choose k
  -- We use: N.descFactorial k / k.descFactorial k = N.choose k
  have hdesc_desc : N.descFactorial k / k.descFactorial k = N.choose k := by
    rw [Nat.descFactorial_eq_factorial_mul_choose N k,
      Nat.descFactorial_eq_factorial_mul_choose k k]
    simp only [Nat.choose_self, mul_one]
    exact Nat.mul_div_cancel_left _ (Nat.factorial_pos k)
  -- Key lemma: (N/k)^k ≤ N.descFactorial k / k.descFactorial k = N.choose k
  -- This is because ∏_{i=0}^{k-1} (N-i)/(k-i) ≥ (N/k)^k
  -- Equivalently: N^k * k.descFactorial k ≤ k^k * N.descFactorial k
  have key : N ^ k * k.descFactorial k ≤ k ^ k * N.descFactorial k := by
    -- Rewrite using products
    rw [hprod, Nat.descFactorial_eq_prod_range k k]
    -- Need: N^k * ∏_{i<k} (k-i) ≤ k^k * ∏_{i<k} (N-i)
    -- Convert N^k and k^k to products
    have hNk : N ^ k = ∏ _ ∈ Finset.range k, N := by rw [Finset.prod_const]; simp
    have hk : k ^ k = ∏ _ ∈ Finset.range k, k := by rw [Finset.prod_const]; simp
    rw [hNk, hk]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod'
    intro i hi
    have hi_lt : i < k := Finset.mem_range.mp hi
    have hNi : i ≤ N := by omega
    have hki : i ≤ k := by omega
    have : N * (k - i) ≤ k * (N - i) := by
      have := Nat.mul_sub_right_distrib N i k
      have := Nat.mul_sub_right_distrib k i N
      nlinarith [Nat.sub_add_cancel hNi, Nat.sub_add_cancel hki]
    exact this
  have hdesc_pos : 0 < k.descFactorial k :=
    (Nat.descFactorial_pos (n := k) (k := k)).mpr (le_refl k)
  have hdiv : k.descFactorial k ∣ N.descFactorial k := by
    rw [Nat.descFactorial_eq_factorial_mul_choose k k,
      Nat.descFactorial_eq_factorial_mul_choose N k]
    simp [Nat.choose_self]
  have h := Nat.le_div_iff_mul_le hdesc_pos |>.mpr key
  rw [Nat.mul_div_assoc _ hdiv] at h
  rwa [hdesc_desc] at h

/-- Comparison with the central binomial coefficient. -/
