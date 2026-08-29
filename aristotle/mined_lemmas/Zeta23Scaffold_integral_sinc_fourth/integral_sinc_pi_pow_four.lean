import Mathlib
/-!
# Integral Sinc Fourth
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_fourth
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

namespace Zeta23Scaffold

open scoped FourierTransform
open MeasureTheory Real Complex

/-! ## The tent function and its Fourier transform -/

/-- The tent (triangle) function, supported on `[-1,1]`. -/

lemma integral_sinc_pi_pow_four : ∫ ξ : ℝ, Real.sinc (π * ξ) ^ 4 = 2 / 3 := by
  set g : ℝ → ℂ := fun ξ => ((Real.sinc (π * ξ) ^ 2 : ℝ) : ℂ) with hgdef
  have hFt : 𝓕 tentC = g := funext fourier_tentC
  have hgint : Integrable g := integrable_sincSq
  have hFtint : Integrable (𝓕 tentC) := by rw [hFt]; exact hgint
  have hinv : ∀ x : ℝ, 𝓕 g x = tentC x := by
    intro x
    have h1 : 𝓕⁻ (𝓕 tentC) = tentC :=
      continuous_tentC.fourierInv_fourier_eq integrable_tentC hFtint
    have h2 : 𝓕⁻ (𝓕 tentC) (-x) = 𝓕 (𝓕 tentC) x := by
      rw [fourierInv_eq_fourier_neg, neg_neg]
    rw [← hFt, ← h2, h1]
    simp [tentC, tent_neg]
  have hmul : ∫ ξ : ℝ, 𝓕 tentC ξ * g ξ = ∫ x : ℝ, tentC x * 𝓕 g x := by
    simpa using VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
      (V := ℝ) (W := ℝ) Real.continuous_fourierChar (by fun_prop) integrable_tentC hgint
  rw [hFt] at hmul
  simp_rw [hinv] at hmul
  have hL : ∫ ξ : ℝ, g ξ * g ξ = ((∫ ξ : ℝ, Real.sinc (π * ξ) ^ 4 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext ξ
    rw [hgdef]
    push_cast
    ring
  have hR : ∫ x : ℝ, tentC x * tentC x = ((2 / 3 : ℝ) : ℂ) := by
    rw [← integral_tent_sq, ← integral_complex_ofReal]
    congr 1
    funext x
    simp only [tentC]
    push_cast
    ring
  rw [hL, hR] at hmul
  exact_mod_cast hmul

