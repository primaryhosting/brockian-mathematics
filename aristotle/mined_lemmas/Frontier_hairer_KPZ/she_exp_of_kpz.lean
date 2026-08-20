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

theorem she_exp_of_kpz (xi : ℝ → ℝ → ℝ) (hu : Regular u) (h : IsKPZSolution xi u) :
    IsSHESolution xi (fun t x => Real.exp (u t x)) := by
  have hpos : ∀ t x, 0 < Real.exp (u t x) := fun t x => Real.exp_pos _
  refine (she_iff_kpz_log xi hpos hu.exp).2 ?_
  have : (fun t x => Real.log (Real.exp (u t x))) = u := by
    funext t x; exact Real.log_exp _
  rw [this]
  exact h

end ColeHopf

/-! ## Well-posedness of KPZ, reduced to the stochastic heat equation

The following is the Cole–Hopf reduction underlying Hairer's solution theory: well-posedness
(existence, uniqueness and, by construction, the explicit solution map) for the KPZ equation
follows from well-posedness of the linear multiplicative stochastic heat equation. -/

/-- **Main theorem (Hairer, KPZ — Cole–Hopf reduction).**  If the multiplicative stochastic heat
equation driven by `xi` is well posed in the class of positive regular functions, then the KPZ
equation driven by `xi` is well posed in the class of regular functions: for every initial
datum `u₀` there is a unique regular solution `u` of `∂ₜ u = ∂ₓ² u + (∂ₓ u)² + ξ` with
`u 0 = u₀`. -/
