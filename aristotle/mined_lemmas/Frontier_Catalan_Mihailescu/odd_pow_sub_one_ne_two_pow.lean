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

lemma odd_pow_sub_one_ne_two_pow {u m n : ℕ} (hu : 3 ≤ u) (hm : 3 ≤ m) (hodd : Odd m) :
    u ^ m ≠ 2 ^ n + 1 := by
  intro heq
  have hdvd : u - 1 ∣ 2 ^ n := by
    have h := Nat.sub_dvd_pow_sub_pow u 1 m
    simp only [one_pow, heq, Nat.add_sub_cancel] at h
    exact h
  obtain ⟨k, hkn, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hk' : u = 2 ^ k + 1 := by omega
  have hk1 : 1 ≤ k := by
    by_contra hc
    have hk0 : k = 0 := by omega
    subst hk0
    simp at hk'
    omega
  obtain ⟨d, hd⟩ : ∃ d, (2 : ℕ) ^ k = 2 * d := ⟨2 ^ (k - 1), by
    rw [← pow_succ']
    congr 1
    omega⟩
  have hd1 : 1 ≤ d := by
    have := Nat.two_pow_pos k
    omega
  have hkk : (2 : ℕ) ^ (k + 1) = 4 * d := by
    have h2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
    omega
  have hu2 : u = 2 * d + 1 := by omega
  have hsq : u ^ 2 ≡ 1 [MOD 2 ^ (k + 1)] := by
    have h1 : u ^ 2 = 2 ^ (k + 1) * (d + 1) + 1 := by rw [hkk, hu2]; ring
    calc u ^ 2 = 2 ^ (k + 1) * (d + 1) + 1 := h1
      _ ≡ 0 + 1 [MOD 2 ^ (k + 1)] := Nat.ModEq.add_right 1 ((Nat.modEq_zero_iff_dvd).2 ⟨d + 1, rfl⟩)
      _ = 1 := by ring
  have hpow : u ^ m ≡ u [MOD 2 ^ (k + 1)] := pow_odd_modEq_self hodd hsq
  have hfin : (2 : ℕ) ^ n ≡ 2 ^ k [MOD 2 ^ (k + 1)] := by
    have h1 : (2 : ℕ) ^ n + 1 ≡ 2 ^ k + 1 [MOD 2 ^ (k + 1)] := by
      calc (2 : ℕ) ^ n + 1 = u ^ m := heq.symm
        _ ≡ u [MOD 2 ^ (k + 1)] := hpow
        _ = 2 ^ k + 1 := hk'
    exact Nat.ModEq.add_right_cancel' 1 h1
  have hn : k + 1 ≤ n := by
    have h3 : u ^ 3 ≤ u ^ m := Nat.pow_le_pow_right (by omega) hm
    have h4 : (2 : ℕ) ^ (k + 1) < 2 ^ n := by
      have hu3 : u ^ 3 = u * u * u := by ring
      nlinarith [heq, hu2, hkk]
    have := (Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)).1 h4
    omega
  exact not_modEq_pow_two hn hfin

/-! ### The solved cases -/

/-- There is no solution of Catalan's equation with `x = 2`: the equation `2 ^ p - y ^ q = 1`
has no solutions with `p, q, y ≥ 2`. -/
