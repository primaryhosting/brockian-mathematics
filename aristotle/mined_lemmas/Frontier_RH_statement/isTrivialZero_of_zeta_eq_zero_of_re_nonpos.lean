import Mathlib

/-!
# RH Statement
Category: Frontier — Moonshot
Target: Frontier.RH_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex
open scoped Real

namespace Frontier

/-- `s` is a *trivial* zero of the Riemann zeta function, i.e. `s = -2, -4, -6, …`. -/

lemma isTrivialZero_of_zeta_eq_zero_of_re_nonpos {s : ℂ} (hre : s.re ≤ 0)
    (hz : riemannZeta s = 0) : IsTrivialZero s := by
  -- `s = 0` is impossible since `ζ 0 = -1/2`.
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [riemannZeta_zero] at hz
    norm_num at hz
  set w : ℂ := 1 - s with hw_def
  have hwre : 1 ≤ w.re := by simp [hw_def, sub_re]; linarith
  have hw1 : w ≠ 1 := by
    intro h
    apply hs0
    have : s = 1 - w := by rw [hw_def]; ring
    rw [this, h, sub_self]
  have hwn : ∀ n : ℕ, w ≠ -n := by
    intro n h
    rw [h] at hwre
    simp at hwre
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hfe := riemannZeta_one_sub hwn hw1
  have hsw : (1 : ℂ) - w = s := by rw [hw_def]; ring
  rw [hsw, hz] at hfe
  -- deduce that the cosine factor vanishes
  have hzw : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hwre
  have hG : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero hwn
  have hpow : ((2 * (π : ℂ)) ^ (-w)) ≠ 0 := by
    apply Complex.cpow_ne_zero_iff.mpr
    left
    have : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    simp [Complex.ofReal_ne_zero.mpr this]
  have hcos : Complex.cos (↑π * w / 2) = 0 := by
    have h := hfe.symm
    rcases mul_eq_zero.mp h with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · rcases mul_eq_zero.mp h2 with h3 | h3
        · rcases mul_eq_zero.mp h3 with h4 | h4
          · norm_num at h4
          · exact absurd h4 hpow
        · exact absurd h3 hG
      · exact h2
    · exact absurd h1 hzw
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hcos
  -- hence `w` is an odd integer `2k+1`
  have hwk : w = 2 * (k : ℂ) + 1 := by
    field_simp at hk
    linear_combination hk
  have hwre' : w.re = 2 * (k : ℝ) + 1 := by rw [hwk]; simp
  have hkre : (0 : ℝ) ≤ (k : ℝ) := by rw [hwre'] at hwre; linarith
  have hs_eq : s = -2 * (k : ℂ) := by
    have : s = 1 - w := by rw [hw_def]; ring
    rw [this, hwk]; ring
  have hk1 : 1 ≤ k := by
    rcases lt_or_ge k 1 with h | h
    · exfalso
      have hk0 : k = 0 := by
        have : (0 : ℤ) ≤ k := by exact_mod_cast hkre
        omega
      apply hs0
      rw [hs_eq, hk0]
      simp
    · exact h
  refine ⟨(k - 1).toNat, ?_⟩
  have : (((k - 1).toNat : ℂ) + 1) = (k : ℂ) := by
    have h1 : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
    have : (((k - 1).toNat : ℂ)) = ((k : ℂ) - 1) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) h1
    rw [this]; ring
  rw [hs_eq, this]

/-- Every nontrivial zero of `ζ` lies in the open critical strip `0 < Re s < 1`.  This is the
unconditional part of the Riemann hypothesis. -/
