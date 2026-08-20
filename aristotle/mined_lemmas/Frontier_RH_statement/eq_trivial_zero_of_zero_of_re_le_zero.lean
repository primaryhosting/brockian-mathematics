/-
# RH Statement
Category: Frontier — Moonshot
Target: Frontier.RH_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# RH Statement
Category: Frontier — Moonshot
Target: Frontier.RH_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex

namespace Frontier

/-- A *nontrivial zero* of the Riemann zeta function: a zero lying in the open critical
strip `0 < Re s < 1`.  All other zeros of `ζ` are the *trivial* zeros `s = -2, -4, -6, …`
(see `Frontier.eq_trivial_zero_of_zero_of_re_le_zero` and
`Frontier.riemannHypothesis_iff`). -/

theorem eq_trivial_zero_of_zero_of_re_le_zero {s : ℂ} (hz : riemannZeta s = 0)
    (hre : s.re ≤ 0) : ∃ n : ℕ, s = -2 * (n + 1) := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, riemannZeta_zero] at hz
    norm_num at hz
  have hwre : 1 ≤ (1 - s).re := by
    simp only [Complex.sub_re, Complex.one_re]; linarith
  have hwne : ∀ n : ℕ, (1 - s) ≠ -n := by
    intro n hn
    have h1 : (1 - s).re = -(n : ℝ) := by rw [hn]; simp
    rw [h1] at hwre
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hwne1 : (1 - s) ≠ 1 := fun h => hs0 (by linear_combination -h)
  have key := riemannZeta_one_sub hwne hwne1
  rw [show (1 : ℂ) - (1 - s) = s by ring, hz] at key
  have hzw : riemannZeta (1 - s) ≠ 0 := riemannZeta_ne_zero_of_one_le_re hwre
  have hG : Complex.Gamma (1 - s) ≠ 0 := Complex.Gamma_ne_zero hwne
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hpow : (2 * (Real.pi : ℂ)) ^ (-(1 - s)) ≠ 0 := by
    apply Complex.cpow_ne_zero_iff_of_exponent_ne_zero ?_ |>.2
    · simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
      exact hpi
    · intro h
      have h1 : s = 1 := by linear_combination h
      rw [h1] at hre
      simp only [Complex.one_re] at hre
      linarith
  have hcos : Complex.cos ((Real.pi : ℂ) * (1 - s) / 2) = 0 := by
    rcases mul_eq_zero.mp key.symm with h | h
    · rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · rcases mul_eq_zero.mp h with h | h
          · norm_num at h
          · exact absurd h hpow
        · exact absurd h hG
      · exact h
    · exact absurd h hzw
  rw [Complex.cos_eq_zero_iff] at hcos
  obtain ⟨k, hk⟩ := hcos
  have hwk : (1 : ℂ) - s = 2 * (k : ℂ) + 1 :=
    mul_left_cancel₀ hpi (by linear_combination 2 * hk)
  have hsk : s = -2 * (k : ℂ) := by linear_combination -hwk
  have hkre : (0 : ℝ) ≤ (k : ℝ) := by
    have h2 : (1 - s).re = 2 * (k : ℝ) + 1 := by rw [hwk]; simp
    rw [h2] at hwre
    linarith
  have hk0 : 0 ≤ k := by exact_mod_cast hkre
  have hk1 : 1 ≤ k := by
    rcases hk0.lt_or_eq with h | h
    · omega
    · exact absurd (by rw [hsk, ← h]; simp) hs0
  refine ⟨(k - 1).toNat, ?_⟩
  have hc : (((k - 1).toNat : ℕ) : ℂ) = (k : ℂ) - 1 := by
    have h1 : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
    exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) h1
  rw [hsk, hc]; ring

/-- `Frontier.CriticalLine` is equivalent to Mathlib's `RiemannHypothesis`. -/
