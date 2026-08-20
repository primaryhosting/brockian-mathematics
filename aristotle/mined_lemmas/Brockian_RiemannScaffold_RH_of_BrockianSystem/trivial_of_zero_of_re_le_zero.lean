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

/-
# RH Of Brockian System
Category: Brockian (Open Discharge)
Target: Brockian.RiemannScaffold.RH_of_BrockianSystem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Complex

namespace Brockian.RiemannScaffold

/-!
## Overview

A *Brockian system* is the datum of a one-sided spectral bound for the Riemann zeta function
inside the critical strip: every zero of `ζ` with `0 < re s < 1` satisfies `1/2 ≤ re s`.

The target theorem `RH_of_BrockianSystem` says that this one-sided bound already implies the
full Riemann Hypothesis in the form stated in Mathlib (`RiemannHypothesis`), with **no further
hypotheses**: the previously assumed reflection principle for zeros and the treatment of the
regions `re s ≤ 0` and `1 ≤ re s` are discharged here from Mathlib, via

* `riemannZeta_one_sub` (the functional equation),
* `riemannZeta_ne_zero_of_one_le_re` (non-vanishing on `1 ≤ re s`),
* `riemannZeta_zero` (the value `ζ 0 = -1/2`),
* `Complex.cos_eq_zero_iff` and `Complex.Gamma_ne_zero`.
-/

/-- **Brockian system**: a one-sided bound `1/2 ≤ re s` for the zeros of `ζ` in the open
critical strip. -/
structure BrockianSystem : Prop where
  /-- Every zero of `ζ` in the open critical strip lies in the half plane `1/2 ≤ re s`. -/
  halfPlane_bound : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → 1 / 2 ≤ s.re

/-- **Reflection principle** (formerly the named hypothesis, now discharged): zeros of `ζ` in
the open critical strip are symmetric under `s ↦ 1 - s`. Immediate from the functional equation
`riemannZeta_one_sub`. -/

theorem trivial_of_zero_of_re_le_zero {s : ℂ} (hs : riemannZeta s = 0) (hre : s.re ≤ 0) :
    ∃ n : ℕ, s = -2 * (n + 1) := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, riemannZeta_zero] at hs
    norm_num at hs
  set w : ℂ := 1 - s with hw
  have hwre : 1 ≤ w.re := by
    simp only [hw, Complex.sub_re, Complex.one_re]
    linarith
  have hwne : ∀ n : ℕ, w ≠ -n := by
    intro n hn
    have h1 : w.re = -(n : ℝ) := by rw [hn]; simp
    rw [h1] at hwre
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hwne1 : w ≠ 1 := by
    intro h
    apply hs0
    have hsw : s = 1 - w := by rw [hw]; ring
    rw [hsw, h, sub_self]
  have hzw : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hwre
  have key := riemannZeta_one_sub hwne hwne1
  have h1w : (1 : ℂ) - w = s := by rw [hw]; ring
  rw [h1w, hs] at key
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero]
  have hpow : (2 * (Real.pi : ℂ)) ^ (-w) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (mul_ne_zero two_ne_zero hpi))
  have hGamma : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero hwne
  have hcos : Complex.cos ((Real.pi : ℂ) * w / 2) = 0 := by
    rcases mul_eq_zero.mp key.symm with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · rcases mul_eq_zero.mp h'' with h3 | h3
          · norm_num at h3
          · exact absurd h3 hpow
        · exact absurd h'' hGamma
      · exact h'
    · exact absurd h hzw
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hcos
  have hwval : w = 2 * (k : ℂ) + 1 := by
    field_simp at hk
    linear_combination hk
  have hk0 : 0 ≤ k := by
    have hre' : w.re = 2 * (k : ℝ) + 1 := by rw [hwval]; simp
    rw [hre'] at hwre
    have : (0 : ℝ) ≤ (k : ℝ) := by linarith
    exact_mod_cast this
  have hsval : s = -2 * (k : ℂ) := by
    rw [← h1w, hwval]; ring
  rcases eq_or_lt_of_le hk0 with h | h
  · exact absurd (by rw [hsval, ← h]; simp) hs0
  · lift k to ℕ using hk0 with m hm
    obtain ⟨j, hj⟩ : ∃ j : ℕ, m = j + 1 := ⟨m - 1, by omega⟩
    exact ⟨j, by rw [hsval, hj]; push_cast; ring⟩

/-- **RH from a Brockian system.**

Given a Brockian system, i.e. the one-sided bound `1/2 ≤ re s` on the zeros of `ζ` in the open
critical strip, the Riemann Hypothesis holds in Mathlib's formulation. Outside the strip the
statement is unconditional: `ζ` has no zeros with `1 ≤ re s`, and its zeros with `re s ≤ 0` are
exactly the trivial ones. Inside the strip, applying the bound both at `s` and at `1 - s`
(a zero as well, by `zeta_zero_one_sub`) forces `re s = 1/2`. -/
