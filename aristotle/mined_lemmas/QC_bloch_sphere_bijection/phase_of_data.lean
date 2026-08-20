import Mathlib

/-!
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QC

open Complex

/-- A normalized qubit state vector: a unit vector in `ℂ²`. -/

lemma phase_of_data (a b a' b' : ℂ) (hv : normSq a + normSq b = 1) (hv' : normSq a' + normSq b' = 1)
    (hna : normSq a = normSq a') (hcj : (starRingEnd ℂ) a * b = (starRingEnd ℂ) a' * b') :
    ∃ c : ℂ, normSq c = 1 ∧ (a', b') = (c * a, c * b) := by
  by_cases ha : a = 0
  · have ha' : a' = 0 := by
      have h0 : normSq a' = 0 := by rw [← hna, ha]; simp
      exact Complex.normSq_eq_zero.mp h0
    have hb : normSq b = 1 := by rw [ha] at hv; simpa using hv
    have hb' : normSq b' = 1 := by rw [ha'] at hv'; simpa using hv'
    have hb0 : b ≠ 0 := fun h => by simp [h] at hb
    refine ⟨b' / b, ?_, ?_⟩
    · rw [Complex.normSq_div, hb, hb']; norm_num
    · simp only [Prod.mk.injEq]
      exact ⟨by rw [ha, ha']; ring, by field_simp⟩
  · have ha0 : normSq a ≠ 0 := fun h => ha (Complex.normSq_eq_zero.mp h)
    have ha0' : normSq a' ≠ 0 := by rw [← hna]; exact ha0
    refine ⟨a' / a, ?_, ?_⟩
    · rw [Complex.normSq_div, hna]
      field_simp
    · simp only [Prod.mk.injEq]
      refine ⟨by field_simp, ?_⟩
      have key : a' * b * (starRingEnd ℂ) a = normSq a' * b' := by
        rw [show a' * b * (starRingEnd ℂ) a = a' * ((starRingEnd ℂ) a * b) by ring, hcj,
          show a' * ((starRingEnd ℂ) a' * b') = (a' * (starRingEnd ℂ) a') * b' by ring,
          Complex.mul_conj]
      have hmc : a * (starRingEnd ℂ) a = normSq a := Complex.mul_conj a
      have hca : (starRingEnd ℂ) a ≠ 0 := by simpa using ha
      have hkey : a' * b = b' * a := by
        refine mul_right_cancel₀ hca ?_
        rw [key, show b' * a * (starRingEnd ℂ) a = (a * (starRingEnd ℂ) a) * b' by ring, hmc, hna]
      field_simp
      linear_combination -hkey

