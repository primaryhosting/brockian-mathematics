import Mathlib
namespace Brockian.MsProth

open Nat in
/-- If `d ∣ k * 2 ^ n` and `2 ^ n ∤ d`, then already `d ∣ k * 2 ^ (n - 1)`. -/

theorem proth (k n N : ℕ) (hk : Odd k) (hkn : k < 2 ^ n) (hN : N = k * 2 ^ n + 1) :
    N.Prime ↔ ∃ a : ZMod N, a ^ ((N - 1) / 2) = -1 := by
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp at hkn
      rcases hk with ⟨m, hm⟩
      omega
    · exact h
  have hk1 : 1 ≤ k := by
    rcases hk with ⟨m, hm⟩; omega
  have hN3 : 3 ≤ N := by
    have : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have : 2 ≤ 2 ^ n := by simpa using this
    nlinarith [hN]
  have hNodd : Odd N := by
    subst hN
    rcases hk with ⟨m, hm⟩
    refine ⟨(k * 2 ^ n) / 2, ?_⟩
    have : 2 ∣ k * 2 ^ n := Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) k
    omega
  constructor
  · intro hprime
    haveI : Fact N.Prime := ⟨hprime⟩
    have hchar : ringChar (ZMod N) ≠ 2 := by
      rw [ZMod.ringChar_zmod_n]
      rintro rfl
      omega
    obtain ⟨a, hanonsq⟩ := FiniteField.exists_nonsquare hchar
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hanonsq (IsSquare.zero)
    refine ⟨a, ?_⟩
    have hNdiv : N / 2 = (N - 1) / 2 := by
      rcases hNodd with ⟨m, hm⟩; omega
    have h1 : a ^ (N / 2) ≠ 1 := fun h => hanonsq ((ZMod.euler_criterion N ha0).2 h)
    have h2 := ZMod.pow_div_two_eq_neg_one_or_one N ha0
    rw [hNdiv] at h1 h2
    tauto
  · rintro ⟨a, ha⟩
    by_contra hnp
    set p := N.minFac with hp_def
    have hp : p.Prime := Nat.minFac_prime (by omega)
    have hpN : p ∣ N := Nat.minFac_dvd N
    have hdvd : 2 ^ n ∣ p - 1 := two_pow_dvd_prime_sub_one hk hn hN a ha hp hpN
    have hp2 : 2 ^ n + 1 ≤ p := by
      have h1 : 0 < p - 1 := by
        have := hp.two_le
        rcases Nat.eq_or_lt_of_le this with h | h
        · exfalso
          have : (2 : ℕ) ∣ N := h ▸ hpN
          rcases hNodd with ⟨m, hm⟩
          omega
        · omega
      have := Nat.le_of_dvd h1 hdvd
      omega
    have hsq : p ^ 2 ≤ N := Nat.minFac_sq_le_self (by omega) hnp
    have : (2 ^ n + 1) ^ 2 ≤ N := le_trans (Nat.pow_le_pow_left hp2 2) hsq
    have hkle : k ≤ 2 ^ n - 1 := by omega
    subst hN
    nlinarith [this, hkn, Nat.one_le_two_pow (n := n)]

end Brockian.MsProth

