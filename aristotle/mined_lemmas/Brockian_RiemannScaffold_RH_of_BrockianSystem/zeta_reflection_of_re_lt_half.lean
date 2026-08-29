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
# RH Of Brockian System
Category: Brockian (Open Discharge)
Target: Brockian.RiemannScaffold.RH_of_BrockianSystem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex
open scoped Real

namespace Brockian.RiemannScaffold

/-- A **Brockian system** for the Riemann zeta function.

The single field records *Brockian half-plane positivity*: the Riemann zeta function has no
zeros strictly to the right of the critical line inside the critical strip.

This is the "open" input of the scaffold: it is not proved here (it is equivalent to the
Riemann hypothesis, see `brockianSystem_iff_riemannHypothesis`).  Everything else in this
file — in particular the reflection step across the critical line, which was previously carried
as a named hypothesis — is discharged unconditionally. -/
structure BrockianSystem : Prop where
  /-- Brockian half-plane positivity: no zeta zeros with `1/2 < Re s < 1`. -/
  no_zero_right_of_critical_line :
    ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → riemannZeta s ≠ 0

/-- If `s` is a nontrivial zero of `ζ` lying strictly to the left of the critical line, then its
reflection `1 - s` is also a zero of `ζ`.

This is the reflection sub-lemma of the Brockian scaffold; it is proved here from the functional
equation, so it no longer has to be assumed. -/

theorem zeta_reflection_of_re_lt_half {s : ℂ} (hz : riemannZeta s = 0)
    (htriv : ¬∃ n : ℕ, s = -2 * (n + 1)) (hlt : s.re < 1 / 2) :
    riemannZeta (1 - s) = 0 := by
  set w : ℂ := 1 - s with hw
  have hwre : 1 / 2 < w.re := by
    simp only [hw, Complex.sub_re, Complex.one_re]
    linarith
  -- `s ≠ 0`, since `ζ 0 = -1/2 ≠ 0`
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [riemannZeta_zero] at hz
    norm_num at hz
  -- side conditions for the functional equation at `w`
  have hwneg : ∀ n : ℕ, w ≠ -n := by
    intro n hn
    have hre : w.re = -(n : ℝ) := by rw [hn]; simp
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [hre] at hwre
    linarith
  have hwone : w ≠ 1 := by
    intro h
    apply hs0
    have hs : s = 1 - w := by rw [hw]; ring
    rw [hs, h, sub_self]
  -- the cosine factor does not vanish
  have hcos : Complex.cos (π * w / 2) ≠ 0 := by
    intro hc
    rw [Complex.cos_eq_zero_iff] at hc
    obtain ⟨k, hk⟩ := hc
    have hpi : (π : ℂ) ≠ 0 := by simp
    have hwk : w = 2 * (k : ℂ) + 1 := by
      field_simp at hk
      linear_combination hk
    have hsk : s = -2 * (k : ℂ) := by
      have hs : s = 1 - w := by rw [hw]; ring
      rw [hs, hwk]; ring
    have hkre : s.re = -2 * (k : ℝ) := by rw [hsk]; simp
    have hk0 : (0 : ℤ) ≤ k := by
      by_contra hcon
      push_neg at hcon
      have hkk : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
      rw [hkre] at hlt
      linarith
    rcases eq_or_lt_of_le hk0 with hk0' | hk1
    · exact hs0 (by rw [hsk, ← hk0']; simp)
    · refine htriv ⟨(k - 1).toNat, ?_⟩
      have hkt : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
      have hcast : (((k - 1).toNat : ℕ) : ℂ) + 1 = (k : ℂ) := by
        have h1 : (((k - 1).toNat : ℕ) : ℂ) = ((k : ℂ) - 1) := by
          exact_mod_cast congrArg (fun m : ℤ => (m : ℂ)) hkt
        rw [h1]; ring
      rw [hsk, ← hcast]
  -- functional equation
  have hfe := riemannZeta_one_sub hwneg hwone
  have h1w : (1 : ℂ) - w = s := by rw [hw]; ring
  rw [h1w, hz] at hfe
  have hwne0 : -w ≠ 0 := by
    intro h
    have hw0 : w = 0 := by simpa using congrArg (fun z => -z) h
    rw [hw0] at hwre
    norm_num at hwre
  have hpow : ((2 * π : ℂ)) ^ (-w) ≠ 0 := by
    refine (Complex.cpow_ne_zero_iff_of_exponent_ne_zero hwne0).mpr ?_
    simp
  have hGamma : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero hwneg
  have hprod := hfe.symm
  simp only [mul_eq_zero] at hprod
  rcases hprod with (((h | h) | h) | h) | h
  · exact absurd h two_ne_zero
  · exact absurd h hpow
  · exact absurd h hGamma
  · exact absurd h hcos
  · exact h

/-- A Brockian system rules out zeta zeros anywhere strictly right of the critical line. -/
