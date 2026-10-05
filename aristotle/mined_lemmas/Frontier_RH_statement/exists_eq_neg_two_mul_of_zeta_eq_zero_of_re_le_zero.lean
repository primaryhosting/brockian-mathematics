/-!
# RH Statement
Category: Frontier — Moonshot
Target: Frontier.RH_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-- `s` is a *nontrivial zero* of the Riemann zeta function if `ζ s = 0` and `s` is not one of
the trivial zeros `-2, -4, -6, …`. -/

theorem exists_eq_neg_two_mul_of_zeta_eq_zero_of_re_le_zero {s : ℂ}
    (hs : riemannZeta s = 0) (hre : s.re ≤ 0) : ∃ n : ℕ, s = -2 * (n + 1) := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [riemannZeta_zero] at hs
    norm_num at hs
  set w : ℂ := 1 - s with hw
  have hwre : 1 ≤ w.re := by
    simp only [hw, Complex.sub_re, Complex.one_re]
    linarith
  have hw1 : w ≠ 1 := by
    intro h
    apply hs0
    have : s = 1 - w := by rw [hw]; ring
    rw [this, h, sub_self]
  have hwn : ∀ n : ℕ, w ≠ -n := by
    intro n hn
    rw [hn] at hwre
    simp only [Complex.neg_re, Complex.natCast_re] at hwre
    have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hfe := riemannZeta_one_sub hwn hw1
  have hsw : (1 : ℂ) - w = s := by rw [hw]; ring
  rw [hsw, hs] at hfe
  have hzw : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hwre
  have hGw : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero hwn
  have hpow : (2 * (Real.pi : ℂ)) ^ (-w) ≠ 0 := by
    apply Complex.cpow_ne_zero_iff.mpr
    left
    have : (Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    simpa using this
  have hcos : Complex.cos ((Real.pi : ℂ) * w / 2) = 0 := by
    have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
    rcases mul_eq_zero.mp hfe.symm with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · rcases mul_eq_zero.mp h'' with h₃ | h₃
          · exact absurd h₃ h2
          · exact absurd h₃ hpow
        · exact absurd h'' hGw
      · exact h'
    · exact absurd h hzw
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hcos
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hwk : w = 2 * (k : ℂ) + 1 := by
    have hmul : (Real.pi : ℂ) * w = (Real.pi : ℂ) * (2 * (k : ℂ) + 1) := by
      linear_combination 2 * hk
    exact mul_left_cancel₀ hpi hmul
  have hsk : s = -2 * (k : ℂ) := by
    have : s = 1 - w := by rw [hw]; ring
    rw [this, hwk]; ring
  have hk1 : 1 ≤ k := by
    rcases lt_or_ge k 1 with h | h
    · exfalso
      have hk0 : k ≤ 0 := by omega
      rcases eq_or_lt_of_le hk0 with h0 | h0
      · exact hs0 (by rw [hsk, h0]; norm_num)
      · have : 0 < s.re := by
          rw [hsk]
          simp only [Complex.mul_re, Complex.neg_re, Complex.ofNat_re, Complex.neg_im,
            Complex.ofNat_im, Complex.intCast_re, Complex.intCast_im]
          have : (k : ℝ) < 0 := by exact_mod_cast h0
          nlinarith
        linarith
    · exact h
  refine ⟨(k - 1).toNat, ?_⟩
  have : ((k - 1).toNat : ℂ) + 1 = (k : ℂ) := by
    have : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
    have h2 : (((k - 1).toNat : ℤ) : ℂ) = ((k - 1 : ℤ) : ℂ) := by exact_mod_cast congrArg _ this
    push_cast at h2 ⊢
    linear_combination h2
  rw [hsk, ← this]

/-- **Reduction of the Riemann Hypothesis to the critical strip.**  The Riemann Hypothesis is
equivalent to the statement that all zeros of `ζ` in the open critical strip `0 < re s < 1`
lie on the critical line `re s = 1/2`. -/
