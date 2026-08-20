import Mathlib
namespace Brockian.MsProth

open Nat in
/-- If `d ∣ k * 2 ^ n` and `2 ^ n ∤ d`, then already `d ∣ k * 2 ^ (n - 1)`. -/

private lemma two_pow_dvd_prime_sub_one {k n N : ℕ} (hk : Odd k) (hn : 1 ≤ n)
    (hN : N = k * 2 ^ n + 1) (a : ZMod N) (ha : a ^ ((N - 1) / 2) = -1)
    {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) : 2 ^ n ∣ p - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hk1 : 1 ≤ k := by rcases hk with ⟨m, hm⟩; omega
  have hpow : 2 ^ n = 2 ^ (n - 1) * 2 := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ]
  have hhalf : (N - 1) / 2 = k * 2 ^ (n - 1) := by
    have h1 : N - 1 = k * 2 ^ (n - 1) * 2 := by rw [hN, Nat.add_sub_cancel, hpow, mul_assoc]
    omega
  have hNodd : ¬ (2 ∣ N) := by
    have : 2 ∣ k * 2 ^ n := Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) k
    omega
  have hp2 : p ≠ 2 := by rintro rfl; exact hNodd hpN
  haveI : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le (Ne.symm hp2)⟩
  set b : ZMod p := (ZMod.castHom hpN (ZMod p)) a with hb_def
  have hb : b ^ (k * 2 ^ (n - 1)) = -1 := by
    have := congrArg (ZMod.castHom hpN (ZMod p)) ha
    rwa [map_pow, map_neg, map_one, hhalf] at this
  have hb2 : b ^ (k * 2 ^ n) = 1 := by
    have hkn : k * 2 ^ n = k * 2 ^ (n - 1) * 2 := by rw [hpow, mul_assoc]
    rw [hkn, pow_mul, hb]
    ring
  have hord : orderOf b ∣ k * 2 ^ n := orderOf_dvd_of_pow_eq_one hb2
  have hnord : ¬ (orderOf b ∣ k * 2 ^ (n - 1)) := by
    intro h
    have h1 : b ^ (k * 2 ^ (n - 1)) = 1 := orderOf_dvd_iff_pow_eq_one.mp h
    rw [hb] at h1
    exact ZMod.neg_one_ne_one h1
  have h2ord : 2 ^ n ∣ orderOf b := by
    by_contra h
    exact hnord (dvd_half_of_not_two_pow_dvd hn hord h)
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, zero_pow (by positivity)] at hb
    exact one_ne_zero (neg_eq_zero.mp hb.symm)
  exact h2ord.trans (orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hb0))

/-- Proth's theorem: for N = k·2ⁿ + 1 with k odd and k < 2ⁿ, N is prime iff there is a with
    a^((N−1)/2) ≡ −1 (mod N). -/
