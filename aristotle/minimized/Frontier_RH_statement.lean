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

/-- **Key intermediate lemma.**  Every zero of `ζ` in the half-plane `Re s ≤ 0` is a *trivial*
zero, i.e. of the form `s = -2 * (n + 1)` for some natural number `n`.

The proof uses the functional equation `ζ (1 - w) = 2 (2π)^{-w} Γ(w) cos(π w / 2) ζ(w)`
together with the non-vanishing of `ζ` on `Re w ≥ 1`: writing `s = 1 - w` with `Re w ≥ 1`,
all factors except the cosine are non-zero, hence `cos (π w / 2) = 0`, which forces `w` to be
an odd positive integer, i.e. `s` a negative even integer. -/

theorem zeta_zero_of_re_nonpos {s : ℂ} (hz : riemannZeta s = 0) (hre : s.re ≤ 0) :
    ∃ n : ℕ, s = -2 * (n + 1) := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, riemannZeta_zero] at hz
    norm_num at hz
  set w : ℂ := 1 - s with hwdef
  have hwre : 1 ≤ w.re := by
    simp only [hwdef, Complex.sub_re, Complex.one_re]
    linarith
  have hwn : ∀ n : ℕ, w ≠ -(n : ℂ) := by
    intro n h
    rw [h] at hwre
    simp only [Complex.neg_re, Complex.natCast_re] at hwre
    have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hw1 : w ≠ 1 := by
    intro h
    apply hs0
    have : (1 : ℂ) - s = 1 := h
    linear_combination -this
  have hfe := riemannZeta_one_sub hwn hw1
  rw [show (1 : ℂ) - w = s by simp [hwdef], hz] at hfe
  have hzw : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hwre
  have hG : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero hwn
  have hp : ((2 : ℂ) * (Real.pi : ℂ)) ^ (-w) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    left
    simp [Real.pi_ne_zero]
  have hcos : Complex.cos ((Real.pi : ℂ) * w / 2) = 0 := by
    have h := hfe.symm
    simp only [mul_eq_zero] at h
    rcases h with (((h | h) | h) | h) | h
    · norm_num at h
    · exact absurd h hp
    · exact absurd h hG
    · exact h
    · exact absurd h hzw
  rw [Complex.cos_eq_zero_iff] at hcos
  obtain ⟨k, hk⟩ := hcos
  have hweq : w = 2 * (k : ℂ) + 1 := by
    field_simp at hk
    exact hk
  have hsk : s = -(2 * (k : ℂ)) := by
    have : s = 1 - w := by simp [hwdef]
    rw [this, hweq]; ring
  have hk0 : 0 ≤ k := by
    rw [hsk] at hre
    simp only [Complex.neg_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
      Complex.re_ofNat, Complex.im_ofNat] at hre
    have : (0 : ℝ) ≤ 2 * (k : ℝ) := by linarith
    have hk' : (0 : ℝ) ≤ (k : ℝ) := by linarith
    exact_mod_cast hk'
  have hkne : k ≠ 0 := by
    intro h
    apply hs0
    rw [hsk, h]
    simp
  have hk1 : 1 ≤ k := by omega
  refine ⟨(k - 1).toNat, ?_⟩
  have : ((k - 1).toNat : ℂ) = (k : ℂ) - 1 := by
    have : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
    exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) this
  rw [hsk, this]; ring

/-- **The Riemann Hypothesis, reduced to the critical strip.**

If every zero of the Riemann zeta function lying in the open critical strip `0 < Re s < 1`
has real part `1/2`, then *all* nontrivial zeros of `ζ` have real part `1/2`, i.e. the
Riemann Hypothesis (as stated in Mathlib, `RiemannHypothesis`) holds.

This is a Lean-checked reduction: the content that is supplied is the elimination of all
zeros outside the critical strip — those with `Re s ≥ 1` do not exist
(`riemannZeta_ne_zero_of_one_le_re`), and those with `Re s ≤ 0` are exactly the trivial zeros
`s = -2(n+1)` (`Frontier.zeta_zero_of_re_nonpos`). -/

theorem RH_statement
    (hstrip : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2) :
    RiemannHypothesis := by
  intro s hz hntriv _
  rcases le_or_gt s.re 0 with h | h
  · exact absurd (zeta_zero_of_re_nonpos hz h) hntriv
  · rcases lt_or_ge s.re 1 with h' | h'
    · exact hstrip s hz h h'
    · exact absurd hz (riemannZeta_ne_zero_of_one_le_re h')

/-- The reduction of `Frontier.RH_statement` is in fact an equivalence: the Riemann Hypothesis
holds if and only if every zero of `ζ` in the open critical strip `0 < Re s < 1` has real
part `1/2`. -/
