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

/-!
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Complex

/-- A pure qubit state: a unit vector in `ℂ²`. -/

theorem blochQuot_injective : Function.Injective blochQuot := by
  refine fun x y => Quotient.inductionOn₂ x y ?_
  rintro v w h
  simp only [blochQuot, Quotient.lift_mk] at h
  -- extract the three coordinate equations
  have h1 : ((starRingEnd ℂ) v.fst * v.snd) = ((starRingEnd ℂ) w.fst * w.snd) := by
    have hre := congrArg (fun p => p.1.1) h
    have him := congrArg (fun p => p.1.2.1) h
    simp only [bloch] at hre him
    apply Complex.ext <;> linarith
  have h2 : normSq v.fst - normSq v.snd = normSq w.fst - normSq w.snd := by
    have := congrArg (fun p => p.1.2.2) h
    simpa [bloch] using this
  have hv := v.norm_eq
  have hw := w.norm_eq
  have ha : normSq v.fst = normSq w.fst := by linarith
  have hb : normSq v.snd = normSq w.snd := by linarith
  apply Quotient.sound
  by_cases hvz : v.fst = 0
  · have hwz : w.fst = 0 := by
      have : normSq w.fst = 0 := by rw [← ha, hvz]; simp
      simpa [Complex.normSq_eq_zero] using this
    have hvs : normSq v.snd = 1 := by
      rw [hvz] at hv; simpa using hv
    have hvs0 : v.snd ≠ 0 := by
      intro hz; rw [hz] at hvs; simp at hvs
    refine ⟨w.snd / v.snd, ?_, ?_, ?_⟩
    · have hws : normSq w.snd = 1 := by rw [← hb, hvs]
      have h1 : ‖w.snd‖ = 1 := by
        have := Complex.normSq_eq_norm_sq w.snd
        rw [hws] at this
        nlinarith [norm_nonneg w.snd]
      have h2 : ‖v.snd‖ = 1 := by
        have := Complex.normSq_eq_norm_sq v.snd
        rw [hvs] at this
        nlinarith [norm_nonneg v.snd]
      rw [norm_div, h1, h2]; norm_num
    · rw [hvz, hwz]; ring
    · field_simp
  · have hwz : w.fst ≠ 0 := by
      intro hz
      apply hvz
      have : normSq v.fst = 0 := by rw [ha, hz]; simp
      simpa [Complex.normSq_eq_zero] using this
    refine ⟨w.fst / v.fst, ?_, ?_, ?_⟩
    · have hvn : ‖v.fst‖ ^ 2 = ‖w.fst‖ ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ha]
      have : ‖v.fst‖ = ‖w.fst‖ := by
        nlinarith [norm_nonneg v.fst, norm_nonneg w.fst]
      rw [norm_div, ← this]
      field_simp
      simpa [Complex.norm_eq_zero] using hvz
    · field_simp
    · -- w.snd = (w.fst / v.fst) * v.snd, i.e. v.fst * w.snd = w.fst * v.snd
      have key : v.fst * w.snd = w.fst * v.snd := by
        have hc : (starRingEnd ℂ) w.fst * (v.fst * w.snd)
            = (starRingEnd ℂ) w.fst * (w.fst * v.snd) := by
          calc (starRingEnd ℂ) w.fst * (v.fst * w.snd)
              = v.fst * ((starRingEnd ℂ) w.fst * w.snd) := by ring
            _ = v.fst * ((starRingEnd ℂ) v.fst * v.snd) := by rw [h1]
            _ = ((normSq v.fst : ℂ)) * v.snd := by
                  rw [← Complex.normSq_eq_conj_mul_self]; ring
            _ = ((normSq w.fst : ℂ)) * v.snd := by rw [ha]
            _ = (starRingEnd ℂ) w.fst * (w.fst * v.snd) := by
                  rw [← Complex.normSq_eq_conj_mul_self]; ring
        have hne : (starRingEnd ℂ) w.fst ≠ 0 := by
          simpa using hwz
        exact mul_left_cancel₀ hne hc
      field_simp
      linear_combination -key

