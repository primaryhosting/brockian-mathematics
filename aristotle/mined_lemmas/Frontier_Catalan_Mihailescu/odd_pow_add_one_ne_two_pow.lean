import Mathlib
/-!
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace Frontier

/-- A *Catalan solution*: a pair of consecutive perfect powers, i.e. natural numbers with
`x ^ p = y ^ q + 1`, all of `x, y, p, q` being at least `2`. -/

lemma odd_pow_add_one_ne_two_pow {u m n : ℕ} (hu : 3 ≤ u) (hm : 3 ≤ m) (hodd : Odd m) :
    u ^ m + 1 ≠ 2 ^ n := by
  intro heq
  have hdvd : u + 1 ∣ u ^ m + 1 := by
    have h := Odd.nat_add_dvd_pow_add_pow u 1 hodd
    simpa using h
  rw [heq] at hdvd
  obtain ⟨k, hkn, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have huodd : Odd u := by
    rcases Nat.even_or_odd u with he | ho
    · exfalso
      obtain ⟨t, ht⟩ := he
      have hk1 : 1 ≤ k := by
        by_contra hc
        have : k = 0 := by omega
        subst this
        simp at hk
        omega
      have : (2 : ℕ) ∣ 2 ^ k := dvd_pow_self 2 (by omega)
      omega
    · exact ho
  obtain ⟨d, hd⟩ := huodd
  have hkk : (2 : ℕ) ^ (k + 1) = 4 * (d + 1) := by
    have h2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
    omega
  have hsq : u ^ 2 ≡ 1 [MOD 2 ^ (k + 1)] := by
    have h1 : u ^ 2 = 2 ^ (k + 1) * d + 1 := by rw [hkk, hd]; ring
    calc u ^ 2 = 2 ^ (k + 1) * d + 1 := h1
      _ ≡ 0 + 1 [MOD 2 ^ (k + 1)] := Nat.ModEq.add_right 1 ((Nat.modEq_zero_iff_dvd).2 ⟨d, rfl⟩)
      _ = 1 := by ring
  have hpow : u ^ m ≡ u [MOD 2 ^ (k + 1)] := pow_odd_modEq_self hodd hsq
  have hfin : (2 : ℕ) ^ n ≡ 2 ^ k [MOD 2 ^ (k + 1)] := by
    calc (2 : ℕ) ^ n = u ^ m + 1 := heq.symm
      _ ≡ u + 1 [MOD 2 ^ (k + 1)] := Nat.ModEq.add_right 1 hpow
      _ = 2 ^ k := hk
  have hn : k + 1 ≤ n := by
    have h3 : u ^ 3 ≤ u ^ m := Nat.pow_le_pow_right (by omega) hm
    have h4 : (2 : ℕ) ^ (k + 1) < 2 ^ n := by
      have hu3 : u ^ 3 = u * u * u := by ring
      nlinarith [heq, hd]
    have := (Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)).1 h4
    omega
  exact not_modEq_pow_two hn hfin

/-- `u ^ m - 1` is never a power of two when `u ≥ 3` and `m ≥ 3` is odd. -/
