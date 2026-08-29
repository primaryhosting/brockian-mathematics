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
def IsTrivialZero (s : ℂ) : Prop := ∃ n : ℕ, s = -2 * (n + 1)

/-- `s` is a *nontrivial* zero of the Riemann zeta function: a zero of `ζ` which is not one of
the trivial zeros `-2, -4, -6, …`. -/
def IsNontrivialZero (s : ℂ) : Prop := riemannZeta s = 0 ∧ ¬ IsTrivialZero s

/-- **The Riemann hypothesis**: every nontrivial zero of `ζ` lies on the critical line
`Re s = 1/2`. -/
def RiemannHypothesisStatement : Prop := ∀ s : ℂ, IsNontrivialZero s → s.re = 1 / 2

/-- The restriction of the Riemann hypothesis to the critical strip `0 < Re s < 1`. -/
def RiemannHypothesisStrip : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1 / 2

/-- Trivial zeros lie strictly to the left of the imaginary axis. -/
lemma re_neg_of_isTrivialZero {s : ℂ} (hs : IsTrivialZero s) : s.re < 0 := by
  obtain ⟨n, rfl⟩ := hs
  simp only [mul_re, neg_re, neg_im, re_ofNat, im_ofNat, add_re, natCast_re, one_re, add_im,
    natCast_im, one_im]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

/-- In the half-plane `Re s ≤ 0` the only zeros of `ζ` are the trivial ones.  This is the
substantive input coming from the functional equation together with the nonvanishing of `ζ`
on `Re s ≥ 1`. -/
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
theorem isNontrivialZero_mem_criticalStrip {s : ℂ} (h : IsNontrivialZero s) :
    0 < s.re ∧ s.re < 1 := by
  obtain ⟨hz, hnt⟩ := h
  refine ⟨?_, ?_⟩
  · by_contra hle
    exact hnt (isTrivialZero_of_zeta_eq_zero_of_re_nonpos (not_lt.mp hle) hz)
  · by_contra hge
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) hz

/-- **Lean-checked reduction of the Riemann hypothesis to the critical strip.**

The full statement — all nontrivial zeros of `ζ` have real part `1/2` — is equivalent to its
restriction to the critical strip `0 < Re s < 1`.  The nontrivial content is that outside the
strip the zeros of `ζ` are completely understood: `ζ` does not vanish on `Re s ≥ 1`, and on
`Re s ≤ 0` its only zeros are the trivial ones `-2, -4, -6, …`. -/
theorem RH_statement : RiemannHypothesisStrip ↔ RiemannHypothesisStatement := by
  constructor
  · intro h s hs
    obtain ⟨hpos, hlt⟩ := isNontrivialZero_mem_criticalStrip hs
    exact h s hpos hlt hs.1
  · intro h s hpos _ hz
    refine h s ⟨hz, ?_⟩
    intro htriv
    linarith [re_neg_of_isTrivialZero htriv]

/-- The formulation above agrees with Mathlib's official statement of the Riemann hypothesis. -/
theorem riemannHypothesisStatement_iff_riemannHypothesis :
    RiemannHypothesisStatement ↔ RiemannHypothesis := by
  constructor
  · intro h s hz hnt _
    exact h s ⟨hz, hnt⟩
  · intro h s ⟨hz, hnt⟩
    refine h s hz hnt ?_
    rintro rfl
    exact absurd hz (riemannZeta_ne_zero_of_one_le_re (by simp))

end Frontier

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

