import Mathlib

/-!
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- The full Catalan–Mihăilescu theorem, as a statement (it is *not* proved in this file):
the only pair of consecutive perfect powers is `8 = 2 ^ 3` and `9 = 3 ^ 2`. -/

lemma catalan_two_pow_sub_one {y p q : ℕ} (hy : 1 < y) (hp : 1 < p) (hq : 1 < q) :
    2 ^ p ≠ y ^ q + 1 := by
  intro h
  have h4 : (4:ℕ) ∣ 2 ^ p := by
    have : (2:ℕ) ^ 2 ∣ 2 ^ p := pow_dvd_pow 2 (by omega)
    simpa using this
  have hyodd : Odd y := by
    rcases Nat.even_or_odd y with he | ho
    · exfalso
      have : Even (y ^ q) := (Nat.even_pow (n := q)).2 ⟨he, by omega⟩
      rcases this with ⟨t, ht⟩
      rcases h4 with ⟨s, hs⟩
      omega
    · exact ho
  obtain ⟨w, hyw, hwe⟩ : ∃ w, y = w + 1 ∧ Even w := by
    rcases hyodd with ⟨t, ht⟩
    exact ⟨2 * t, by omega, ⟨t, by ring⟩⟩
  subst hyw
  rcases Nat.even_or_odd q with hqe | hqo
  · -- even exponent: `2 ^ p ≡ 2 (mod 4)`, impossible
    obtain ⟨k, rfl⟩ := hqe
    have hZ : Odd ((w + 1) ^ k) := hyodd.pow
    rcases hZ with ⟨t, ht⟩
    have hsplit : (w + 1) ^ (k + k) = ((w + 1) ^ k) * ((w + 1) ^ k) := by rw [← pow_add]
    rcases h4 with ⟨s, hs⟩
    rw [hsplit, ht] at h
    have : (2 * t + 1) * (2 * t + 1) + 1 = 4 * (t * t + t) + 2 := by ring
    omega
  · -- odd exponent: `y + 1` carries the full power of two
    obtain ⟨m, rfl⟩ := hqo
    have hm : 1 ≤ m := by omega
    have hkey := geom_alt_nat w m
    set C := (∑ k ∈ Finset.range m, (w + 1) ^ (2 * k + 1) * w) + 1 with hC
    have hCodd : Odd C := by
      have hev : Even (∑ k ∈ Finset.range m, (w + 1) ^ (2 * k + 1) * w) := by
        apply Finset.even_sum
        intro i _
        exact hwe.mul_left _
      rcases hev with ⟨t, ht⟩
      exact ⟨t, by omega⟩
    have hCdvd : C ∣ 2 ^ p := ⟨w + 2, by omega⟩
    obtain ⟨i, hi, hCi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hCdvd
    have hC1 : C = 1 := by
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · simpa using hCi
      · exfalso
        rw [hCi] at hCodd
        rcases hCodd with ⟨t, ht⟩
        have h2 : (2:ℕ) ∣ 2 ^ i := dvd_pow_self 2 hipos.ne'
        omega
    rw [hC1, one_mul] at hkey
    have hge : (w + 1) ^ 2 ≤ (w + 1) ^ (2 * m + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hw1 : 1 ≤ w := by omega
    nlinarith [hge, hkey]

/-- **Catalan's equation with a prime power on the smaller side.**
`x ^ p = r ^ n + 1` with `r` prime, `x, p, n > 1` forces `9 = 8 + 1`. -/
