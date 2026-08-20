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

theorem centralBinom_mul_pow_le {N k : ℕ} (hkN : 2 * k ≤ N) :
    Nat.centralBinom k * N ^ k ≤ (2 * k) ^ k * N.choose k := by
  have key : (2 * k).descFactorial k * N ^ k ≤ (2 * k) ^ k * N.descFactorial k := by
    rw [Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range]
    have hNk : N ^ k = ∏ _ ∈ Finset.range k, N := by rw [Finset.prod_const]; simp
    have h2k : (2 * k) ^ k = ∏ _ ∈ Finset.range k, (2 * k) := by rw [Finset.prod_const]; simp
    rw [hNk, h2k, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod'
    intro i hi
    have hi_lt : i < k := Finset.mem_range.mp hi
    have h1 : i ≤ 2 * k := by omega
    have h2 : i ≤ N := by omega
    nlinarith [Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
  have e1 : (2 * k).descFactorial k = k.factorial * Nat.centralBinom k := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    rfl
  have e2 : N.descFactorial k = k.factorial * N.choose k :=
    Nat.descFactorial_eq_factorial_mul_choose N k
  rw [e1, e2] at key
  have key2 : k.factorial * (Nat.centralBinom k * N ^ k)
      ≤ k.factorial * ((2 * k) ^ k * N.choose k) := by
    calc k.factorial * (Nat.centralBinom k * N ^ k)
        = k.factorial * Nat.centralBinom k * N ^ k := by ring
      _ ≤ (2 * k) ^ k * (k.factorial * N.choose k) := key
      _ = k.factorial * ((2 * k) ^ k * N.choose k) := by ring
  exact Nat.le_of_mul_le_mul_left key2 (Nat.factorial_pos k)

/-- The main lower bound. -/
