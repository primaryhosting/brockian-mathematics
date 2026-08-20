import Mathlib
/-!
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Real Complex
open scoped FourierTransform

noncomputable section

namespace Zeta23Scaffold

/-- The tent function `t ↦ max (1 - |t|) 0`. -/

lemma integral_tent_mul (g : ℝ → ℂ) :
    ∫ v : ℝ, g v * tent v = ∫ v in (-1 : ℝ)..1, g v * ((1 - |v| : ℝ) : ℂ) := by
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Set.Ioc (-1 : ℝ) 1) (f := fun v => g v * tent v)]
  · apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro v hv
    simp only [Set.mem_Ioc] at hv
    have h1 : |v| ≤ 1 := abs_le.2 ⟨hv.1.le, hv.2⟩
    simp [tent, tentR_of_mem h1]
  · intro x hx
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
    have h1 : 1 ≤ |x| := by
      rcases hx with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_nonneg (by linarith)]; linarith
    simp [tent, tentR_eq_zero h1]

/-- Folding the tent integral onto `[0, 1]`, where the oscillating factor becomes a cosine. -/
