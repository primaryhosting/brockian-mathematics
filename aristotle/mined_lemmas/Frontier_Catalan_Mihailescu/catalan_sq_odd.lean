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

lemma catalan_sq_odd {x y q : ℕ} (hy : 1 < y) (hq : 2 ≤ q) (hodd : Odd y) :
    x ^ 2 ≠ y ^ q + 1 := by
  intro h
  have hyq : Odd (y ^ q) := hodd.pow
  have hx2 : Even (x ^ 2) := by
    rcases hyq with ⟨k, hk⟩
    exact ⟨k + 1, by omega⟩
  have hxe : Even x := by
    rcases Nat.even_or_odd x with he | ho
    · exact he
    · exact absurd hx2 (by simpa using (ho.pow (n := 2)))
  have hy3 : 3 ≤ y := by
    rcases hodd with ⟨k, hk⟩; omega
  have hyq3 : 9 ≤ y ^ q := by
    calc (9:ℕ) = 3 ^ 2 := by norm_num
    _ ≤ y ^ q := Nat.pow_le_pow_left hy3 2 |>.trans (Nat.pow_le_pow_right (by omega) hq)
  have hx4 : 4 ≤ x := by nlinarith [h, hyq3]
  obtain ⟨c, rfl⟩ : ∃ c, x = c + 1 := ⟨x - 1, by omega⟩
  have hfac : c * (c + 2) = y ^ q := by ring_nf; ring_nf at h; omega
  have hcop : Nat.Coprime c (c + 2) := by
    have hd : Nat.gcd c (c + 2) ∣ 2 := by
      have h1 : Nat.gcd c (c + 2) ∣ (c + 2) - c :=
        Nat.dvd_sub (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
      simpa using h1
    have hoddc : Odd c := by rcases hxe with ⟨m, hm⟩; exact ⟨m - 1, by omega⟩
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h1 | h1
    · exact h1
    · exfalso
      have : (2:ℕ) ∣ c := h1 ▸ Nat.gcd_dvd_left c (c + 2)
      rcases hoddc with ⟨m, hm⟩; omega
  obtain ⟨b, hb⟩ : ∃ b, c = b ^ q :=
    exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr hcop) hfac
  obtain ⟨a, ha⟩ : ∃ a, c + 2 = a ^ q :=
    exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr hcop.symm) (by rw [mul_comm]; exact hfac)
  have hb1 : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with rfl | hbp
    · rw [zero_pow (by omega)] at hb; omega
    · omega
  have hab : b < a := by
    by_contra hc
    push_neg at hc
    have := Nat.pow_le_pow_left hc q
    omega
  have h1 : (b + 1) ^ q ≤ a ^ q := Nat.pow_le_pow_left hab q
  have h2 := succ_pow_ge b q hb1 hq
  omega

/-- `x ^ p = y ^ q + 1` has no solutions with `p` even and `y` odd. -/
