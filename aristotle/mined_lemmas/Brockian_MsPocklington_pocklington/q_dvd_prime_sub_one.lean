import Mathlib
namespace Brockian.MsPocklington

/-- If `p` is a prime divisor of `N` and `gcd (a ^ m - 1) N = 1`, then `a ^ m ≢ 1 (mod p)`. -/

private lemma q_dvd_prime_sub_one {N q m a p : ℕ} (hfac : N - 1 = q * m)
    (hq : q.Prime) (h1 : a ^ (N - 1) ≡ 1 [MOD N]) (h2 : Nat.gcd (a ^ m - 1) N = 1)
    (hp : p.Prime) (hpN : p ∣ N) : q ∣ p - 1 := by
  -- Since p ∣ N and a^(N-1) ≡ 1 (mod N), we have a^(N-1) ≡ 1 (mod p)
  have hmod_p : a ^ (N - 1) ≡ 1 [MOD p] := h1.of_dvd hpN
  rw [hfac] at hmod_p
  -- The order of a mod p divides q * m
  -- But a^m ≢ 1 (mod p) by pow_ne_one_mod_prime
  have hnamod : ¬(a ^ m ≡ 1 [MOD p]) := pow_ne_one_mod_prime h2 hp hpN
  -- Consider the order of a in ZMod p
  have horder : orderOf (a : ZMod p) ∣ q * m := by
    rw [orderOf_dvd_iff_pow_eq_one]
    have hconv : (a : ZMod p) ^ (q * m) = 1 := by
      simpa using congr_arg (fun x : ℕ => (x : ZMod p)) hmod_p
    exact hconv
  -- The order does not divide m
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hnot_dvd : ¬(orderOf (a : ZMod p) ∣ m) := by
    intro hdvd
    have hpow := orderOf_dvd_iff_pow_eq_one.mp hdvd
    apply hnamod
    have hcast : ((a ^ m : ℕ) : ZMod p) = 1 := by rw [Nat.cast_pow]; exact hpow
    rw [show (1 : ZMod p) = ((1 % p : ℕ) : ZMod p) from by
      simp [Nat.mod_eq_of_lt hp.one_lt]] at hcast
    rw [ZMod.natCast_eq_natCast_iff] at hcast
    rwa [Nat.mod_eq_of_lt hp.one_lt] at hcast
  -- Apply prime_dvd_of_dvd_mul_not_dvd to get q ∣ order
  have hq_dvd_order : q ∣ orderOf (a : ZMod p) := prime_dvd_of_dvd_mul_not_dvd hq horder hnot_dvd
  -- The order divides p - 1 since ZMod p has p - 1 nonzero elements
  have ha_ne_zero : (a : ZMod p) ≠ 0 := by
    intro ha0
    have hp_div_a : p ∣ a := (ZMod.natCast_eq_zero_iff a p).mp ha0
    have hm_pos : m ≠ 0 := by
      by_contra hm0
      simp [hm0] at hnot_dvd
    have hqm : q * m ≠ 0 := Nat.mul_ne_zero hq.pos.ne' hm_pos
    have hpow : a ^ (q * m) ≡ 0 [MOD p] :=
      (Nat.modEq_zero_iff_dvd).mpr (dvd_pow hp_div_a hqm)
    have hcontra : 1 ≡ 0 [MOD p] := (hmod_p.symm).trans hpow
    simp [Nat.ModEq, Nat.mod_eq_of_lt hp.one_lt] at hcontra
  have horder_p_minus_1 : orderOf (a : ZMod p) ∣ p - 1 := orderOf_dvd_iff_pow_eq_one.mpr (ZMod.pow_card_sub_one_eq_one ha_ne_zero)
  exact Nat.dvd_trans hq_dvd_order horder_p_minus_1

/-- Every prime divisor of `N` is bigger than `q`. -/
