/-
# Hairer KPZ
Category: Frontier — Fields Medal Work
Target: Frontier.hairer_KPZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hairer KPZ
Category: Frontier — Fields Medal Work
Target: Frontier.hairer_KPZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace Frontier

/-! ## Space-time functions and partial derivatives

A space-time function is modelled as `u : ℝ → ℝ → ℝ`, where `u t x` is its value at time `t`
and space point `x`. -/

/-- Time derivative of a space-time function. -/

theorem she_wellposed_of_kpz_wellposed (xi : ℝ → ℝ → ℝ)
    (hKPZ : ∀ u₀ : ℝ → ℝ, ∃! u : ℝ → ℝ → ℝ,
      Regular u ∧ (∀ x, u 0 x = u₀ x) ∧ IsKPZSolution xi u)
    (Z₀ : ℝ → ℝ) (hZ₀ : ∀ x, 0 < Z₀ x) :
    ∃! Z : ℝ → ℝ → ℝ,
      ((∀ t x, 0 < Z t x) ∧ Regular Z) ∧ (∀ x, Z 0 x = Z₀ x) ∧ IsSHESolution xi Z := by
  obtain ⟨u, ⟨hureg, huinit, hu⟩, huniq⟩ := hKPZ (fun x => Real.log (Z₀ x))
  refine ⟨fun t x => Real.exp (u t x), ⟨⟨fun t x => Real.exp_pos _, hureg.exp⟩, ?_,
    she_exp_of_kpz xi hureg hu⟩, ?_⟩
  · intro x
    show Real.exp (u 0 x) = Z₀ x
    rw [huinit x, Real.exp_log (hZ₀ x)]
  · rintro W ⟨⟨hWpos, hWreg⟩, hWinit, hW⟩
    have hWu : (fun t x => Real.log (W t x)) = u := by
      refine huniq _ ⟨hWreg.log hWpos, ?_, (she_iff_kpz_log xi hWpos hWreg).1 hW⟩
      intro x
      show Real.log (W 0 x) = Real.log (Z₀ x)
      rw [hWinit x]
    funext t x
    have h : Real.log (W t x) = u t x := congrFun (congrFun hWu t) x
    rw [← h, Real.exp_log (hWpos t x)]

/-! ## Base case: the spatially homogeneous KPZ equation -/

/-- For a space-time function that does not depend on the space variable, both space derivatives
vanish. -/
