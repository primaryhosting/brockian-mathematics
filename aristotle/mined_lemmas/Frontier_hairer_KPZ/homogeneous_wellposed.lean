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

open scoped BigOperators Real Classical NNReal

set_option maxHeartbeats 1000000

namespace KPZ

/-- Spatial derivative of a space-time function `h : time → space → ℝ`. -/

theorem homogeneous_wellposed (g : ℝ → ℝ) (hg : Continuous g) (h₀ : ℝ) :
    ∃! H : ℝ → ℝ, H 0 = h₀ ∧ IsSolution (fun t _ => g t) (fun t _ => H t) := by
  refine ⟨fun t => h₀ + ∫ s in (0 : ℝ)..t, g s, ⟨by simp, ?_⟩, ?_⟩
  · rw [isSolution_of_const_space]
    intro t
    simpa using ((hg.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add h₀
  · rintro H ⟨hH0, hHsol⟩
    rw [isSolution_of_const_space] at hHsol
    have hgoal : ∀ t, HasDerivAt (fun u => h₀ + ∫ s in (0 : ℝ)..u, g s) (g t) t := by
      intro t
      simpa using ((hg.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add h₀
    set G : ℝ → ℝ := fun t => h₀ + ∫ s in (0 : ℝ)..t, g s with hG
    have hdiff : Differentiable ℝ (fun t => H t - G t) := fun t =>
      ((hHsol t).sub (hgoal t)).differentiableAt
    have hzero : ∀ t, deriv (fun t => H t - G t) t = 0 := by
      intro t
      have := (hHsol t).sub (hgoal t)
      simpa using this.deriv
    have hconst := is_const_of_deriv_eq_zero hdiff hzero
    funext t
    have h1 := hconst t 0
    have h2 : G 0 = h₀ := by simp [hG]
    have : H t - G t = H 0 - G 0 := h1
    rw [hH0, h2] at this
    linarith [this]

/-! ## The reduction: well-posedness from the abstract fixed point problem

Hairer's solution theory recasts the (renormalised) KPZ equation as a fixed point
problem `u = Φ d u` in a complete metric space `X` of modelled distributions, where
`d` ranges over the data (an admissible model together with an initial condition).
The two analytic inputs are:

* `Φ d` is a contraction on `X`, uniformly in `d` (short-time Schauder estimates);
* `Φ` depends Lipschitz-continuously on the data `d` (continuity of the abstract
  integration and reconstruction operators in the model).

The theorem below is the Lean-checked reduction: from these two inputs one obtains
a *well-posed* problem, i.e. a solution map `S` which exists, is unique, and depends
Lipschitz-continuously (in particular continuously) on the data. -/

