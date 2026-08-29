import Mathlib

/-!
# Prime Power Member Structure
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.primePower_member_structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ArithmeticFunction Finset

namespace Brockian
namespace BetrothedNumbers

/-- `IsBetrothedPair m n` says that `(m, n)` is a betrothed (quasi-amicable) pair: two distinct
positive integers, each of whose sum of divisors equals `m + n + 1`. -/

theorem primePower_member_structure {p a n : ℕ} (hp : p.Prime) (ha : 0 < a)
    (h : IsBetrothedPair (p ^ a) n) :
    Odd p ∧ Odd a ∧ 3 < a ∧ Even n := by
  obtain ⟨hm0, hn0, hne, hsm, hsn⟩ := h
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  rw [sigma_one_apply_prime_pow hp] at hsm
  set u := ∑ k ∈ range b, p ^ k with hu
  have hstep : ∑ k ∈ range (b + 1 + 1), p ^ k = p * u + 1 + p ^ (b + 1) := by
    rw [Finset.sum_range_succ, geom_sum_succ_eq]
  rw [hstep] at hsm
  -- the partner is `n = p * u` with `u = 1 + p + ⋯ + p ^ (b-1)`
  have hnu : n = p * u := by omega
  have hb1 : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp [hu] at hnu; omega
    · exact hb
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  have huw : u = p * (∑ k ∈ range c, p ^ k) + 1 := by rw [hu, geom_sum_succ_eq]
  have hcop : Nat.Coprime p u := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    rw [huw] at hd
    have h1 : p ∣ 1 := (Nat.dvd_add_right (dvd_mul_right p _)).mp hd
    have := Nat.le_of_dvd one_pos h1
    have := hp.two_le
    omega
  have hsigman : sigma 1 n = (p + 1) * sigma 1 u := by
    rw [hnu, isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_one_prime hp]
  -- `p` is odd
  have hp2 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with hp2 | hp2
    · exfalso
      subst hp2
      have hu1 : u + 1 = 2 ^ (c + 1) := by rw [hu]; exact two_geom_sum (c + 1)
      have h2c : 2 ^ (c + 1) % 2 = 0 := by
        have : (2:ℕ) ^ (c + 1) = 2 * 2 ^ c := by ring
        omega
      have huodd : u % 2 = 1 := by omega
      have hpa : 2 ^ (c + 1 + 1) % 2 = 0 := by
        have : (2:ℕ) ^ (c + 1 + 1) = 2 * 2 ^ (c + 1) := by ring
        omega
      have hsnodd : sigma 1 n % 2 = 1 := by omega
      have hsu : sigma 1 u % 2 = 1 := by
        rw [hsigman, Nat.mul_mod] at hsnodd
        omega
      obtain ⟨r, hr⟩ := exists_sq_of_odd_sigma_one u huodd hsu
      rcases Nat.eq_zero_or_pos c with rfl | hc
      · have hu1' : u = 1 := by simp [hu]
        have h2 : sigma 1 2 = 3 := by decide
        rw [hnu, hu1'] at hsn
        norm_num [h2] at hsn
      · have h4 : (2:ℕ) ^ (c + 1) = 4 * 2 ^ (c - 1) := by
          rw [show c + 1 = 2 + (c - 1) by omega, pow_add]
          norm_num
        have hu4 : u % 4 = 3 := by omega
        have hrr : r * r % 4 = r % 4 * (r % 4) % 4 := Nat.mul_mod r r 4
        have hlt : r % 4 < 4 := Nat.mod_lt _ (by norm_num)
        interval_cases h : r % 4 <;> omega
    · exact hp2
  -- the partner is even, and the exponent is odd
  have hp1 : (p + 1) % 2 = 0 := by omega
  have hpar : sigma 1 n % 2 = 0 := by rw [hsigman, Nat.mul_mod, hp1, zero_mul]; simp
  have hpa : p ^ (c + 1 + 1) % 2 = 1 := by rw [Nat.pow_mod, hp2]; simp
  have hn2 : n % 2 = 0 := by omega
  have hu2 : u % 2 = 0 := by
    rw [hnu] at hn2
    simp [Nat.mul_mod, hp2] at hn2
    omega
  have hc2 : c % 2 = 1 := by
    rw [hu, geom_sum_mod_two hp2] at hu2
    omega
  -- the exponent is not `3`
  have hc1 : c ≠ 1 := by
    intro hc
    subst hc
    have hu' : u = p + 1 := by rw [hu]; simp [Finset.sum_range_succ]; omega
    have h1 : sigma 1 n = (p + 1) * sigma 1 (p + 1) := by rw [hsigman, hu']
    have h2 : sigma 1 n = (p + 1) * (p * p + 1) := by
      rw [hsn, hnu, hu']; ring
    have hkey : sigma 1 (p + 1) = p * p + 1 :=
      Nat.eq_of_mul_eq_mul_left (by omega) (h1 ▸ h2)
    have hb := two_mul_sigma_one_le (p + 1)
    rw [hkey] at hb
    have hple : p ≤ 3 := by nlinarith [hp.two_le]
    have hp3 : p = 3 := by have := hp.two_le; omega
    subst hp3
    have h7 : sigma 1 (3 + 1) = 7 := by decide
    omega
  refine ⟨Nat.odd_iff.mpr hp2, Nat.odd_iff.mpr (by omega), by omega, Nat.even_iff.mpr hn2⟩

/-- Both members of a betrothed pair cannot be prime powers. -/
