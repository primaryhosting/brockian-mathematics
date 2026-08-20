import Mathlib
import PerfectNumbersEuler

namespace Brockian.EvenPerfectMod9

open Nat

/-- The modular-arithmetic consequence of the Euclid–Euler form of an even perfect number. -/
lemma euclidEuler_form_mod9 {k : ℕ} (hprime : Nat.Prime (mersenne (k + 1)))
    (hlarge : 6 < 2 ^ k * mersenne (k + 1)) :
    (2 ^ k * mersenne (k + 1)) % 9 = 1 := by
  have hmersenne_def : mersenne (k + 1) = 2 ^ (k + 1) - 1 := rfl
  -- Establish bounds on k
  have hk_pos : k ≠ 0 := by
    rintro rfl
    simp [mersenne] at hprime
    exact Nat.not_prime_one hprime
  have hk_ge_2 : 2 ≤ k := by
    by_contra h
    push_neg at h
    interval_cases k <;> simp [mersenne] at hlarge hprime
  -- k+1 is odd (since k+1 ≥ 3 and prime implies k+1 is odd), so k is even
  have hk_even : Even k := by
    have hk1_ge_3 : 3 ≤ k + 1 := by omega
    -- If k is odd, then k+1 is even and ≥ 4, so 2^(k+1) - 1 is divisible by 3
    by_contra hk_odd
    have hk_mod : k % 2 = 1 := by
      have := Nat.even_or_odd k
      cases this with
      | inl heven => exact absurd heven hk_odd
      | inr hodd => exact Nat.odd_iff.mp hodd
    -- k+1 is even
    have hk1_even : Even (k + 1) := by
      rw [even_iff_two_dvd]
      omega
    -- mersenne(k+1) is divisible by 3 when k+1 is even
    have h3_div : 3 ∣ mersenne (k + 1) := by
      simp [mersenne]
      have hk1_eq : k + 1 = 2 * ((k + 1) / 2) := by omega
      rw [hk1_eq, pow_mul]
      have : 3 ∣ 2^2 - 1 := by norm_num
      have hfactor : (2^2 - 1) ∣ (2^2)^((k+1)/2) - 1 := by
        have := nat_sub_dvd_pow_sub_pow (2^2) 1 ((k+1)/2)
        simpa using this
      exact dvd_trans ‹3 ∣ 2^2 - 1› hfactor
    -- Since mersenne(k+1) is prime and divisible by 3, it must equal 3
    have hmersenne_eq_3 : mersenne (k + 1) = 3 := by
      have := hprime.dvd_iff_eq (by norm_num : 3 ≠ 1)
      exact this.mp h3_div
    -- But mersenne(k+1) = 3 implies k+1 = 2, contradicting k+1 ≥ 3
    rw [mersenne] at hmersenne_eq_3
    have h2k1 : 2^(k+1) = 2^2 := by norm_num at hmersenne_eq_3 ⊢; omega
    have : k + 1 = 2 := Nat.pow_right_injective (by norm_num : 1 < 2) h2k1
    omega
  -- Now use modular arithmetic: k is even, so k % 6 ∈ {0, 2, 4}
  -- For each case, 2^k * mersenne(k+1) ≡ 1 (mod 9)
  have hk_mod6 : k % 6 = 0 ∨ k % 6 = 2 ∨ k % 6 = 4 := by
    have := hk_even
    rw [even_iff_two_dvd] at this
    omega
  -- Reduce to finite computation using Nat.pow_mod
  rw [mersenne]
  have h2k_mod : 2 ^ k % 9 = 2 ^ (k % 6) % 9 := by
    conv_lhs => rw [← Nat.mod_add_div k 6, pow_add, pow_mul]
    norm_num [Nat.mul_mod, Nat.pow_mod]
  have h2k1_mod : 2 ^ (k + 1) % 9 = 2 ^ ((k + 1) % 6) % 9 := by
    conv_lhs => rw [← Nat.mod_add_div (k + 1) 6, pow_add, pow_mul]
    norm_num [Nat.mul_mod, Nat.pow_mod]
  -- Do case analysis on k % 6
  rcases hk_mod6 with hk0 | hk2 | hk4
  · -- k % 6 = 0
    simp [hk0] at h2k_mod
    have hk1_mod : (k + 1) % 6 = 1 := by omega
    simp [hk1_mod] at h2k1_mod
    -- 2^(k+1) % 9 = 2, so (2^(k+1) - 1) % 9 = 1
    have hmersenne_mod : (2 ^ (k + 1) - 1) % 9 = 1 := by
      have : 2 ^ (k + 1) % 9 = 2 := h2k1_mod
      have hpos : 0 < 2 ^ (k + 1) := by positivity
      omega
    calc (2 ^ k * (2 ^ (k + 1) - 1)) % 9
        = ((2 ^ k % 9) * ((2 ^ (k + 1) - 1) % 9)) % 9 := by rw [Nat.mul_mod]
      _ = (1 * 1) % 9 := by rw [h2k_mod, hmersenne_mod]
      _ = 1 := by norm_num
  · -- k % 6 = 2
    simp [hk2] at h2k_mod
    have hk1_mod : (k + 1) % 6 = 3 := by omega
    simp [hk1_mod] at h2k1_mod
    -- 2^(k+1) % 9 = 8, so (2^(k+1) - 1) % 9 = 7
    have hmersenne_mod : (2 ^ (k + 1) - 1) % 9 = 7 := by
      have : 2 ^ (k + 1) % 9 = 8 := h2k1_mod
      have hpos : 0 < 2 ^ (k + 1) := by positivity
      omega
    calc (2 ^ k * (2 ^ (k + 1) - 1)) % 9
        = ((2 ^ k % 9) * ((2 ^ (k + 1) - 1) % 9)) % 9 := by rw [Nat.mul_mod]
      _ = (4 * 7) % 9 := by rw [h2k_mod, hmersenne_mod]
      _ = 1 := by norm_num
  · -- k % 6 = 4
    simp [hk4] at h2k_mod
    have hk1_mod : (k + 1) % 6 = 5 := by omega
    simp [hk1_mod] at h2k1_mod
    -- 2^(k+1) % 9 = 5, so (2^(k+1) - 1) % 9 = 4
    have hmersenne_mod : (2 ^ (k + 1) - 1) % 9 = 4 := by
      have : 2 ^ (k + 1) % 9 = 5 := h2k1_mod
      have hpos : 0 < 2 ^ (k + 1) := by positivity
      omega
    calc (2 ^ k * (2 ^ (k + 1) - 1)) % 9
        = ((2 ^ k % 9) * ((2 ^ (k + 1) - 1) % 9)) % 9 := by rw [Nat.mul_mod]
      _ = (7 * 4) % 9 := by rw [h2k_mod, hmersenne_mod]
      _ = 1 := by norm_num

/-- Every even perfect number greater than 6 is congruent to 1 modulo 9. -/
theorem even_perfect_mod9 {n : ℕ} (he : Even n) (hp : Nat.Perfect n) (h6 : 6 < n) : n % 9 = 1 := by
  obtain ⟨k, hprime, rfl⟩ :=
    PerfectNumbersEuler.Nat.eq_two_pow_mul_prime_mersenne_of_even_perfect he hp
  exact euclidEuler_form_mod9 hprime h6

end Brockian.EvenPerfectMod9
