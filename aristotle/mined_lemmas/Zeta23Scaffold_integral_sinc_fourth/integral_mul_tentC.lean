/-
# Integral Sinc Fourth
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_fourth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Integral Sinc Fourth
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_fourth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

We prove `∫ x : ℝ, (sin x / x) ^ 4 = 2 * π / 3`.

The argument is the classical Fourier-analytic one.  Let `tent` be the triangle function
`t ↦ max (1 - |t|) 0`.  Its Fourier transform is `ξ ↦ sinc (π ξ) ^ 2`.  The multiplication
(Parseval) formula `∫ 𝓕 f * g = ∫ f * 𝓕 g`, applied with `f = tent` and `g = 𝓕 tent`,
together with Fourier inversion (`𝓕 (𝓕 tent) = tent ∘ neg`), gives

`∫ sinc (π ξ) ^ 4 dξ = ∫ tent ^ 2 = 2 / 3`,

and a change of variables `x = π ξ` yields the result.
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

open MeasureTheory FourierTransform Real Complex

/-- The tent (triangle) function, supported on `[-1, 1]`. -/

lemma integral_mul_tentC {g : ℝ → ℂ} (hg : Continuous g) :
    ∫ t : ℝ, g t * tentC t =
      (∫ t in (-1 : ℝ)..0, g t * (1 + 1 * (t : ℂ))) +
        ∫ t in (0 : ℝ)..1, g t * (1 + (-1) * (t : ℂ)) := by
  have h0 : ∀ t : ℝ, t ∉ Set.Icc (-1 : ℝ) 1 → g t * tentC t = 0 := by
    intro t ht
    simp [tentC_eq_zero_of_notMem ht]
  have hcont : Continuous fun t : ℝ => g t * tentC t := hg.mul continuous_tentC
  have hstep : ∫ t : ℝ, g t * tentC t = ∫ t in (-1 : ℝ)..1, g t * tentC t := by
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero h0,
      MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have hsplit : ∫ t in (-1 : ℝ)..1, g t * tentC t =
      (∫ t in (-1 : ℝ)..0, g t * tentC t) + ∫ t in (0 : ℝ)..1, g t * tentC t :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)).symm
  have e1 : ∫ t in (-1 : ℝ)..0, g t * tentC t
      = ∫ t in (-1 : ℝ)..0, g t * (1 + 1 * (t : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at ht
    obtain ⟨h1, h2⟩ := ht
    have : tent t = 1 + t := by
      unfold tent; rw [abs_of_nonpos h2, max_eq_left (by linarith)]; ring
    simp only [tentC, this]
    push_cast
    ring
  have e2 : ∫ t in (0 : ℝ)..1, g t * tentC t
      = ∫ t in (0 : ℝ)..1, g t * (1 + (-1) * (t : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    obtain ⟨h1, h2⟩ := ht
    have : tent t = 1 - t := by
      unfold tent; rw [abs_of_nonneg h1, max_eq_left (by linarith)]
    simp only [tentC, this]
    push_cast
    ring
  rw [hstep, hsplit, e1, e2]

/-- The antiderivative computation `∫ exp (c t) (A + B t) dt`. -/
