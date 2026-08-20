import Mathlib
import GeometryOfNumbers.Legendre.Main
namespace Brockian.LegendreThreeSquare
/-- Legendre's three-square theorem: n is a sum of three squares iff n is NOT of the
    form 4^a·(8b+7). -/

lemma squarefree_part_mod_eight_six (n s m : ℕ) (heq : n = s^2 * m) (hn : n % 8 = 6) :
    m % 8 = 6 := by
  have hs_odd : s % 2 = 1 := by
    by_contra h_even
    have h2s : 2 ∣ s := Nat.dvd_iff_mod_eq_zero.mpr (Nat.mod_two_ne_one.mp h_even)
    have h4s2 : 4 ∣ s^2 := by
      obtain ⟨k, rfl⟩ := h2s
      use k^2; ring
    have h4n : 4 ∣ n := by
      rw [heq]
      exact dvd_mul_of_dvd_left h4s2 m
    have hn4_zero : n % 4 = 0 := Nat.mod_eq_zero_of_dvd h4n
    have hn4_six : n % 4 = 6 % 4 := by
      rw [← Nat.mod_mod_of_dvd n (by decide : 4 ∣ 8), hn]
    rw [hn4_zero] at hn4_six
    norm_num at hn4_six

  have hs_sq_mod : s^2 % 8 = 1 := by
    have h_cases : s % 8 = 1 ∨ s % 8 = 3 ∨ s % 8 = 5 ∨ s % 8 = 7 := by
      have h2 : (s % 8) % 2 = s % 2 := Nat.mod_mod_of_dvd s (by decide : 2 ∣ 8)
      rw [hs_odd] at h2
      match h8 : s % 8 with
      | 1 => left; rfl
      | 3 => right; left; rfl
      | 5 => right; right; left; rfl
      | 7 => right; right; right; rfl
      | 0|2|4|6 =>
        rw [h8] at h2
        contradiction
      | _ =>
        have : s % 8 < 8 := Nat.mod_lt s (by decide)
        omega
    rcases h_cases with h1 | h3 | h5 | h7
    · simp [Nat.pow_mod, h1]
    · simp [Nat.pow_mod, h3]
    · simp [Nat.pow_mod, h5]
    · simp [Nat.pow_mod, h7]

  have h_mod : n % 8 = (s^2 % 8 * (m % 8)) % 8 := by
    rw [heq, Nat.mul_mod]
  rw [hn, hs_sq_mod, one_mul] at h_mod
  exact (Nat.mod_mod m 8).symm.trans h_mod.symm

/-- Scaling lemma: if `m` is a sum of three squares, then so is `s^2 * m`. -/
