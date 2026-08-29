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
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex

namespace QC

/-- A pure state of a qubit: a unit vector `(a, b)` in `ℂ²`. -/
structure Qubit where
  a : ℂ
  b : ℂ
  unit : normSq a + normSq b = 1

/-- Two pure qubit states are equivalent when they differ by a global phase. -/

lemma phase_of_bloch_eq {a b c d : ℂ} (h1 : normSq a + normSq b = 1)
    (h2 : normSq c + normSq d = 1) (hprod : a * (starRingEnd ℂ) b = c * (starRingEnd ℂ) d)
    (hz : normSq a - normSq b = normSq c - normSq d) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ c = z * a ∧ d = z * b := by
  have hac : normSq a = normSq c := by linarith
  have hbd : normSq b = normSq d := by linarith
  have hnorm_ac : ‖a‖ = ‖c‖ := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hac
    nlinarith [norm_nonneg a, norm_nonneg c]
  have hnorm_bd : ‖b‖ = ‖d‖ := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hbd
    nlinarith [norm_nonneg b, norm_nonneg d]
  by_cases ha : a = 0
  · have hc : c = 0 := by
      have : ‖c‖ = 0 := by rw [← hnorm_ac, ha]; simp
      simpa using this
    have hb : b ≠ 0 := by
      intro hb0
      rw [ha, hb0] at h1; simp at h1
    refine ⟨d / b, ?_, by simp [ha, hc], by field_simp⟩
    rw [norm_div, ← hnorm_bd, div_self (by simpa using hb)]
  · refine ⟨c / a, ?_, by field_simp, ?_⟩
    · rw [norm_div, ← hnorm_ac, div_self (by simpa using ha)]
    · have hnz : normSq (c / a) = 1 := by
        rw [Complex.normSq_eq_norm_sq, norm_div, ← hnorm_ac,
          div_self (by simpa using ha)]; norm_num
      have key : (starRingEnd ℂ) b = (c / a) * (starRingEnd ℂ) d := by
        field_simp
        rw [mul_comm] at hprod ⊢
        linear_combination hprod
      have hb' : b = (starRingEnd ℂ) (c / a) * d := by
        have := congrArg (starRingEnd ℂ) key
        simpa [map_mul] using this
      rw [hb', ← mul_assoc, Complex.mul_conj, hnz]
      simp

