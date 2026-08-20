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

/-- A pure qubit state: a unit vector `(a, b)` in `ℂ²`. -/
structure Qubit where
  a : ℂ
  b : ℂ
  norm_eq : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1

/-- A point of the 2-sphere `S² ⊆ ℝ³`. -/
@[ext]
structure Sphere2 where
  x : ℝ
  y : ℝ
  z : ℝ
  norm_eq : x ^ 2 + y ^ 2 + z ^ 2 = 1


lemma blochRaw_inj {v w : Qubit} (h : blochRaw v = blochRaw w) : PhaseEq v w := by
  have hna := norm_a_eq h
  have hnb := norm_b_eq h
  have hp := conj_mul_eq h
  by_cases hva : v.a = 0
  · have hwa : w.a = 0 := by
      have : ‖w.a‖ = 0 := by rw [← hna, hva]; simp
      simpa using this
    have hvb : v.b ≠ 0 := by
      intro h0
      have := v.norm_eq
      rw [hva, h0] at this
      simp at this
    have hwb : w.b ≠ 0 := by
      intro h0
      apply hvb
      have : ‖v.b‖ = 0 := by rw [hnb, h0]; simp
      simpa using this
    refine ⟨w.b / v.b, ?_, ?_, ?_⟩
    · rw [norm_div, hnb]
      exact div_self (by simpa using hwb)
    · rw [hva, hwa]; ring
    · field_simp
  · have hwa : w.a ≠ 0 := by
      intro h0
      apply hva
      have : ‖v.a‖ = 0 := by rw [hna, h0]; simp
      simpa using this
    have hns : Complex.normSq v.a = Complex.normSq w.a := by
      rw [← Complex.sq_norm, ← Complex.sq_norm, hna]
    have hcc : (starRingEnd ℂ) w.a ≠ 0 := by simpa using hwa
    have key : w.b * v.a = w.a * v.b := by
      apply mul_right_cancel₀ hcc
      calc w.b * v.a * (starRingEnd ℂ) w.a
          = ((starRingEnd ℂ) w.a * w.b) * v.a := by ring
        _ = ((starRingEnd ℂ) v.a * v.b) * v.a := by rw [hp]
        _ = (v.a * (starRingEnd ℂ) v.a) * v.b := by ring
        _ = ((Complex.normSq v.a : ℝ) : ℂ) * v.b := by rw [Complex.mul_conj]
        _ = ((Complex.normSq w.a : ℝ) : ℂ) * v.b := by rw [hns]
        _ = (w.a * (starRingEnd ℂ) w.a) * v.b := by rw [Complex.mul_conj]
        _ = w.a * v.b * (starRingEnd ℂ) w.a := by ring
    refine ⟨w.a / v.a, ?_, ?_, ?_⟩
    · rw [norm_div, hna]
      exact div_self (by simpa using hwa)
    · field_simp
    · field_simp
      linear_combination key

