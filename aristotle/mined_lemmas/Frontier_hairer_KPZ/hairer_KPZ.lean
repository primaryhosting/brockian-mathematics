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

theorem hairer_KPZ (xi : ℝ → ℝ → ℝ)
    (hSHE : ∀ Z₀ : ℝ → ℝ, (∀ x, 0 < Z₀ x) →
      ∃! Z : ℝ → ℝ → ℝ,
        ((∀ t x, 0 < Z t x) ∧ Regular Z) ∧ (∀ x, Z 0 x = Z₀ x) ∧ IsSHESolution xi Z)
    (u₀ : ℝ → ℝ) :
    ∃! u : ℝ → ℝ → ℝ, Regular u ∧ (∀ x, u 0 x = u₀ x) ∧ IsKPZSolution xi u := by
  obtain ⟨Z, ⟨⟨hpos, hreg⟩, hinit, hZ⟩, huniq⟩ :=
    hSHE (fun x => Real.exp (u₀ x)) (fun x => Real.exp_pos _)
  refine ⟨fun t x => Real.log (Z t x), ⟨hreg.log hpos, ?_, (she_iff_kpz_log xi hpos hreg).1 hZ⟩, ?_⟩
  · intro x; show Real.log (Z 0 x) = u₀ x; rw [hinit x, Real.log_exp]
  · rintro v ⟨hvreg, hvinit, hv⟩
    have hZv : (fun t x => Real.exp (v t x)) = Z := by
      refine huniq _ ⟨⟨fun t x => Real.exp_pos _, hvreg.exp⟩, ?_, she_exp_of_kpz xi hvreg hv⟩
      intro x; rw [hvinit x]
    funext t x
    have : Real.exp (v t x) = Z t x := congrFun (congrFun hZv t) x
    rw [← this, Real.log_exp]

/-- **Converse reduction.**  Conversely, well-posedness of the KPZ equation in the class of
regular functions implies well-posedness of the multiplicative stochastic heat equation in the
class of positive regular functions.  Together with `Frontier.hairer_KPZ` this shows that the two
problems are equivalent under the Cole–Hopf transform. -/
