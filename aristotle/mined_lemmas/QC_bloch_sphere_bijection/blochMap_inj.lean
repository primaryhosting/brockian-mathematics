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

/-! ## Pure qubit states -/

/-- A pure state of a single qubit: a unit vector `a|0⟩ + b|1⟩` in `ℂ²`. -/
structure Qubit where
  /-- amplitude of `|0⟩` -/
  a : ℂ
  /-- amplitude of `|1⟩` -/
  b : ℂ
  /-- normalization -/
  norm_eq : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1

namespace Qubit

/-- Two qubit states are physically identical when they differ by a global phase. -/

theorem blochMap_inj {v w : Qubit} (h : blochMap v = blochMap w) : Qubit.PhaseRel v w := by
  rw [blochMap_eq_iff] at h
  obtain ⟨hx, hy, hz⟩ := h
  -- equal off-diagonal products
  have hprod : (starRingEnd ℂ) v.a * v.b = (starRingEnd ℂ) w.a * w.b := by
    apply Complex.ext
    · have := hx; rw [blochX, blochX] at this; linarith
    · have := hy; rw [blochY, blochY] at this; linarith
  -- equal moduli
  have hz' : ‖v.a‖ ^ 2 - ‖v.b‖ ^ 2 = ‖w.a‖ ^ 2 - ‖w.b‖ ^ 2 := hz
  have hsa : ‖v.a‖ ^ 2 = ‖w.a‖ ^ 2 := by
    have h1 := v.norm_eq; have h2 := w.norm_eq; linarith
  have hsb : ‖v.b‖ ^ 2 = ‖w.b‖ ^ 2 := by
    have h1 := v.norm_eq; have h2 := w.norm_eq; linarith
  have hna : ‖v.a‖ = ‖w.a‖ := by
    nlinarith [norm_nonneg v.a, norm_nonneg w.a]
  have hnb : ‖v.b‖ = ‖w.b‖ := by
    nlinarith [norm_nonneg v.b, norm_nonneg w.b]
  by_cases hva : v.a = 0
  · -- then both first amplitudes vanish and the second ones are unit
    have hwa : w.a = 0 := by
      have : ‖w.a‖ = 0 := by rw [← hna, hva, norm_zero]
      simpa using this
    have hvb : v.b ≠ 0 := by
      intro h0
      have := v.norm_eq
      rw [hva, h0] at this
      simp at this
    refine ⟨w.b / v.b, ?_, ?_, ?_⟩
    · have hbne : ‖w.b‖ ≠ 0 := by
        rw [← hnb]; simpa using hvb
      rw [norm_div, hnb, div_self hbne]
    · rw [hva, hwa, mul_zero]
    · field_simp
  · refine ⟨w.a / v.a, ?_, ?_, ?_⟩
    · rw [norm_div, hna]
      have : ‖w.a‖ ≠ 0 := by
        rw [← hna]; simpa using hva
      field_simp
    · field_simp
    · -- key cross relation: w.a * v.b = v.a * w.b
      have hcross : w.a * v.b = v.a * w.b := by
        have hmul : w.a * ((starRingEnd ℂ) v.a * v.b) = w.a * ((starRingEnd ℂ) w.a * w.b) := by
          rw [hprod]
        have h1 : w.a * ((starRingEnd ℂ) w.a * w.b) = ((‖w.a‖ : ℂ) ^ 2) * w.b := by
          rw [← mul_assoc, Complex.mul_conj']
        have h2 : w.a * ((starRingEnd ℂ) v.a * v.b) = (starRingEnd ℂ) v.a * (w.a * v.b) := by
          ring
        have h3 : ((‖w.a‖ : ℂ) ^ 2) * w.b = ((‖v.a‖ : ℂ) ^ 2) * w.b := by rw [hna]
        have h4 : ((‖v.a‖ : ℂ) ^ 2) * w.b = (starRingEnd ℂ) v.a * (v.a * w.b) := by
          rw [← Complex.conj_mul']
          ring
        have hca : (starRingEnd ℂ) v.a ≠ 0 := by
          simpa using hva
        rw [h2, h1, h3, h4] at hmul
        exact mul_left_cancel₀ hca hmul
      field_simp
      linear_combination -hcross

/-! ## Surjectivity -/

