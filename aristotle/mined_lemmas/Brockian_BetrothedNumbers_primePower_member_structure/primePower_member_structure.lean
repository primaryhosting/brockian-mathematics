/-
# Prime Power Member Structure
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.primePower_member_structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Prime Power Member Structure
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.primePower_member_structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace Brockian.BetrothedNumbers

/-- `m` and `n` form a *betrothed* (quasi-amicable) pair: both are positive, distinct, and the
sum of the divisors of each equals `m + n + 1` (equivalently, the sum of the *proper* divisors of
each one is the other one plus one). -/

theorem primePower_member_structure {p a n : ℕ} (hp : p.Prime)
    (h : IsBetrothedPair (p ^ a) n) : Odd p ∧ Odd a ∧ 3 < a ∧ Even n := by
  obtain ⟨hm0, hn0, hne, hsm, hsn⟩ := h
  have hpair : IsBetrothedPair (p ^ a) n := ⟨hm0, hn0, hne, hsm, hsn⟩
  have hgs : n + 1 = ∑ i ∈ Finset.range a, p ^ i := partner_eq hp hpair
  -- `a ≥ 1`, say `a = b + 1`
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := by
    cases a with
    | zero => simp at hgs
    | succ b => exact ⟨b, rfl⟩
  rw [geom_sum_succ] at hgs
  -- `b ≥ 1`, say `b = c + 1`
  have hb1 : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp only [Finset.range_zero, Finset.sum_empty, Nat.mul_zero] at hgs; omega
    · exact hb
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  -- name the geometric sum `G = 1 + p + ⋯ + p ^ c`; the partner is `n = p * G`
  obtain ⟨G, hG⟩ : ∃ G, ∑ i ∈ Finset.range (c + 1), p ^ i = G := ⟨_, rfl⟩
  rw [hG] at hgs
  have hnG : n = p * G := by omega
  have hGc : G = p * (∑ i ∈ Finset.range c, p ^ i) + 1 := by rw [← hG, geom_sum_succ]
  have hcop : Nat.Coprime p G := by rw [hGc]; simp
  have hG0 : 0 < G := by rw [hGc]; positivity
  -- the sum-of-divisors of the partner factors as `(p + 1) * σ 1 G`
  have hsplit : σ 1 n = (p + 1) * σ 1 G := by
    rw [hnG, isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_one_prime hp]
  rcases hp.eq_two_or_odd' with rfl | hpodd
  · -- `p = 2` is impossible
    exfalso
    have hGpow : G + 1 = 2 ^ (c + 1) := by rw [← hG]; exact geom_sum_two _
    have hpow : (2 : ℕ) ^ (c + 1 + 1) = 2 * (G + 1) := by rw [pow_succ, hGpow]; ring
    -- the defining equation becomes `3 * σ 1 G = 4 * G + 3`
    have key : 3 * σ 1 G = 4 * G + 3 := by
      rw [hsplit, hpow] at hsn
      omega
    -- hence `3 ∣ G`
    have h3 : 3 ∣ G := by omega
    obtain ⟨r, rfl⟩ := h3
    rcases Nat.lt_or_ge r 2 with hr | hr
    · interval_cases r
      · omega
      · -- `G = 3`
        have h31 : σ 1 (3 * 1) = 4 := by decide
        omega
    · rcases eq_or_ne r 3 with rfl | hr3
      · -- `G = 9` would force `2 ^ (c + 1) = 10`
        have h5 : (5 : ℕ) ∣ 2 ^ (c + 1) := ⟨2, by omega⟩
        have h52 : (5 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num) h5
        omega
      · -- four distinct divisors of `G` already overshoot
        have := sigma_one_three_mul_ge hr hr3
        omega
  · -- `p` is odd
    have hp2 : p % 2 = 1 := Nat.odd_iff.mp hpodd
    -- `σ 1 n` is even, since `p + 1` divides it
    have heven : Even (σ 1 n) := by
      rw [hsplit]; exact (hpodd.add_one).mul_right _
    have hnEven : Even n := by
      have h1 : σ 1 n % 2 = 0 := Nat.even_iff.mp heven
      have h2 : p ^ (c + 1 + 1) % 2 = 1 := Nat.odd_iff.mp hpodd.pow
      rw [Nat.even_iff]
      omega
    -- hence `G` is even, hence `c` is odd, hence `a = c + 2` is odd
    have hGeven : Even G := by
      have hev : Even (p * G) := hnG ▸ hnEven
      rcases Nat.even_mul.mp hev with hh | hh
      · exact absurd hh (Nat.not_even_iff_odd.mpr hpodd)
      · exact hh
    have hGeven' : G % 2 = 0 := Nat.even_iff.mp hGeven
    have hcodd : c % 2 = 1 := by
      have hpar := geom_sum_mod_two hpodd (c + 1)
      rw [hG] at hpar
      omega
    refine ⟨hpodd, by rw [Nat.odd_iff]; omega, ?_, hnEven⟩
    -- it remains to rule out `a = 3`, i.e. `c = 1`
    by_contra hcon
    have hc1 : c = 1 := by omega
    subst hc1
    have hGval : G = 1 + p := by rw [← hG]; simp [Finset.sum_range_succ]
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have e1 : σ 1 n = (p + 1) * σ 1 (1 + p) := by rw [hsplit, hGval]
    rw [e1, hnG, hGval] at hsn
    have hkey : (p + 1) * σ 1 (1 + p) = (p + 1) * (p ^ 2 + 1) := by rw [hsn]; ring
    have hsig : σ 1 (1 + p) = p ^ 2 + 1 := Nat.eq_of_mul_eq_mul_left (by omega) hkey
    have hbound := two_mul_sigma_one_le (1 + p)
    rw [hsig] at hbound
    have hple : p ≤ 3 := by nlinarith
    have hpeq : p = 3 := by omega
    subst hpeq
    have h4 : σ 1 (1 + 3) = 7 := by decide
    rw [h4] at hsig
    norm_num at hsig

/-- Sanity check (non-vacuity): `(48, 75)` is a betrothed pair, since
`σ 1 48 = σ 1 75 = 124 = 48 + 75 + 1`. -/
