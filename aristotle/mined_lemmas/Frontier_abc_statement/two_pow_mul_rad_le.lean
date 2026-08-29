import Mathlib

/-!
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Frontier

/-- The radical of a natural number: the product of its distinct prime factors. -/

lemma two_pow_mul_rad_le {x k : ℕ} (hx : x ≠ 0) (hdvd : 2 ^ k ∣ x) :
    2 ^ k * rad x ≤ 2 * x := by
  classical
  set K := x.factorization 2 with hK
  have hkK : k ≤ K := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hx).mp hdvd
  set m := x / 2 ^ K with hm
  have hxm : 2 ^ K * m = x := Nat.ordProj_mul_ordCompl_eq_self x 2
  set r' := ∏ p ∈ x.primeFactors \ {2}, p with hr'
  have hr'dvdrad : r' ∣ rad x :=
    Finset.prod_dvd_prod_of_subset _ _ _ Finset.sdiff_subset
  have hr'dvd : r' ∣ x := hr'dvdrad.trans (rad_dvd x)
  have hr'cop : Nat.Coprime r' (2 ^ K) := by
    refine Nat.Coprime.pow_right _ ?_
    refine Nat.Coprime.prod_left ?_
    intro p hp
    rw [Finset.mem_sdiff] at hp
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp.1) Nat.prime_two).mpr
      (by simpa using hp.2)
  have hr'm : r' ∣ m := hr'cop.dvd_of_dvd_mul_left (by rw [hxm]; exact hr'dvd)
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exact absurd (by rw [← hxm, h, mul_zero]) hx
    · exact h
  have hr'le : r' ≤ m := Nat.le_of_dvd hmpos hr'm
  calc 2 ^ k * rad x ≤ 2 ^ K * (2 * r') :=
        Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hkK) (rad_le_two_mul_odd_part x)
    _ = 2 * (2 ^ K * r') := by ring
    _ ≤ 2 * (2 ^ K * m) := by
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hr'le)
    _ = 2 * x := by rw [hxm]

/-- `2 ^ (n + 3) ∣ 3 ^ (2 ^ (n + 1)) - 1`. -/
