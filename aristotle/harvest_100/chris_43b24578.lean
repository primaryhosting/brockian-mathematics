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

import Mathlib

/-!
# RH Statement
Category: Frontier — Moonshot
Target: Frontier.RH_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The Riemann Hypothesis asserts that all nontrivial zeros of the Riemann zeta function `ζ`
have real part `1/2`.  Mathlib provides the formal statement as `RiemannHypothesis`:

`∀ (s : ℂ), riemannZeta s = 0 → ¬(∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 → s.re = 1 / 2`.

The Riemann Hypothesis itself is open, so what is proved here is a *Lean-checked reduction*:
the main theorem `Frontier.RH_statement` shows that `RiemannHypothesis` is **equivalent** to the
apparently weaker assertion that every zero of `ζ` inside the critical strip `0 < re s < 1`
lies on the critical line `re s = 1/2`.

The nontrivial content is the "zero-free region" direction: any zero of `ζ` which is neither
a trivial zero `-2, -4, -6, …` nor the pole `s = 1` must lie in the critical strip.  This is
proved from Mathlib's non-vanishing theorem on `re s ≥ 1` together with the functional equation.
-/

namespace Frontier

open Complex

/-- A *nontrivial zero* of the Riemann zeta function: a zero of `ζ` which is not one of the
trivial zeros `-2, -4, -6, …` (and is not the point `s = 1`, where Mathlib's `riemannZeta`
takes a junk value). -/
def IsNontrivialZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ (¬ ∃ n : ℕ, s = -2 * (n + 1)) ∧ s ≠ 1

/-- A zero of `ζ` with `re s ≤ 0` is necessarily one of the trivial zeros `-2, -4, -6, …`.
This is proved from the functional equation together with the non-vanishing of `ζ` on
`re s ≥ 1`. -/
theorem trivial_of_zero_of_re_nonpos {s : ℂ} (h : riemannZeta s = 0) (h0 : s.re ≤ 0) :
    ∃ n : ℕ, s = -2 * (n + 1) := by
  by_contra hnt
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [riemannZeta_zero] at h
    norm_num at h
  set w : ℂ := 1 - s with hw
  have hwre : 1 ≤ w.re := by simp [hw, Complex.sub_re]; linarith
  have hwn : ∀ n : ℕ, w ≠ -n := by
    intro n hn
    rw [hn] at hwre
    simp at hwre
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hw1 : w ≠ 1 := by
    simp only [hw, ne_eq, sub_eq_self]
    exact hs0
  have key := riemannZeta_one_sub hwn hw1
  rw [show (1 : ℂ) - w = s by rw [hw]; ring, h] at key
  have hz : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hwre
  have hg : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hp : ((2 * (Real.pi : ℂ)) ^ (-w)) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    push_neg
    intro hc
    exact absurd hc (by simp [Real.pi_ne_zero])
  have hcos : Complex.cos (Real.pi * w / 2) = 0 := by
    have hk := key.symm
    rcases mul_eq_zero.1 hk with h1 | h1
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · rcases mul_eq_zero.1 h2 with h3 | h3
        · rcases mul_eq_zero.1 h3 with h4 | h4
          · norm_num at h4
          · exact absurd h4 hp
        · exact absurd h3 hg
      · exact h2
    · exact absurd h1 hz
  rw [Complex.cos_eq_zero_iff] at hcos
  obtain ⟨k, hk⟩ := hcos
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hwk : w = 2 * (k : ℂ) + 1 := by field_simp at hk; exact hk
  have hsk : s = -2 * (k : ℂ) := by
    have hws : (1 : ℂ) - s = 2 * k + 1 := by rw [← hw]; exact hwk
    linear_combination -hws
  have hkre : (0 : ℝ) ≤ (k : ℝ) := by
    have hre : s.re = -2 * (k : ℝ) := by rw [hsk]; simp
    rw [hre] at h0; linarith
  have hk1 : 1 ≤ k := by
    have hk0 : 0 ≤ k := by exact_mod_cast hkre
    rcases eq_or_lt_of_le hk0 with heq | hlt
    · exact absurd (by rw [hsk, ← heq]; simp : s = 0) hs0
    · omega
  exact hnt ⟨(k - 1).toNat, by
    have hc : ((k - 1).toNat : ℂ) = (k : ℂ) - 1 := by
      have h2 : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
      exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) h2
    rw [hc, hsk]; ring⟩

/-- Every nontrivial zero of `ζ` lies in the critical strip `0 < re s < 1`. -/
theorem isNontrivialZero_mem_critical_strip {s : ℂ} (hs : IsNontrivialZero s) :
    0 < s.re ∧ s.re < 1 := by
  obtain ⟨hzero, hntriv, _⟩ := hs
  constructor
  · by_contra hcon
    push_neg at hcon
    exact hntriv (trivial_of_zero_of_re_nonpos hzero hcon)
  · by_contra hcon
    push_neg at hcon
    exact riemannZeta_ne_zero_of_one_le_re hcon hzero

/-- **Riemann Hypothesis, Lean-checked reduction.**

The statement "all nontrivial zeros of `ζ` have real part `1/2`" (Mathlib's
`RiemannHypothesis`) is equivalent to the statement that every zero of `ζ` inside the
critical strip `0 < re s < 1` lies on the critical line `re s = 1/2`.

Thus RH may be verified by examining only the critical strip: all other zeros of `ζ` are
automatically the trivial zeros `-2, -4, -6, …`. -/
theorem RH_statement :
    RiemannHypothesis ↔
      ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2 := by
  constructor
  · intro hRH s hzero hlow hhigh
    refine hRH s hzero ?_ ?_
    · rintro ⟨n, rfl⟩
      rw [show ((-2 * ((n : ℂ) + 1)).re) = -2 * ((n : ℝ) + 1) by simp] at hlow
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    · rintro rfl
      simp at hhigh
  · intro hstrip s hzero hntriv hne
    obtain ⟨hlow, hhigh⟩ := isNontrivialZero_mem_critical_strip ⟨hzero, hntriv, hne⟩
    exact hstrip s hzero hlow hhigh

end Frontier

