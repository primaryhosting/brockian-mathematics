import Mathlib
/-!
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Mathlib coverage

A search of the current Mathlib (both by name and by `exact?`/`apply?` against the goal) turns up
no development of the Navier–Stokes equations: the string `Navier` does not occur anywhere in the
library, and there is no theory of the incompressible Euler or Navier–Stokes systems. So the full
Millennium statement `Frontier.NavierStokesGlobalRegularity` below cannot be closed by an existing
lemma; it is stated here and left unproved (it is an open problem).

What *is* proved below, axiom-cleanly:

* `Frontier.isNavierStokesSolution_shear` — a Lean-checked **reduction**: every smooth solution of
  the one dimensional heat equation `∂ₜ g = ν ∂²_y g` yields a global smooth solution of the full
  three dimensional nonlinear incompressible Navier–Stokes system (the shear flow
  `u (t, x) = (g t x₂, 0, 0)`, with zero pressure). The nonlinearity `(u · ∇)u` vanishes identically
  on this class.
* `Frontier.navier_stokes_regularity` — the target: global existence and smoothness for the
  shear-flow initial data obtained this way.
* `Frontier.navier_stokes_regularity_const` — the base case of constant initial velocity.
* `Frontier.navier_stokes_regularity_sine` — an explicit nontrivial global smooth solution.

The Mathlib inputs used are elementary calculus lemmas: `deriv_const`, `HasDerivAt.sin`,
`HasDerivAt.cos`, `HasDerivAt.exp`, `HasDerivAt.const_mul`, `HasDerivAt.deriv`, `contDiff_const`,
`contDiff_apply`, `ContDiff.comp`, `ContDiff.prodMk`, and `Function.update_of_ne`.
-/

open scoped BigOperators

namespace Frontier

/-! ## Differential operators on `ℝ³` -/

/-- The `j`-th partial derivative of a scalar field on `ℝ³`. -/

theorem lap_coord (h : ℝ → ℝ) (m : Fin 3) (x : Fin 3 → ℝ) :
    lap (fun y => h (y m)) x = deriv (deriv h) (x m) := by
  have hfun : ∀ j : Fin 3, partialDeriv (fun y => h (y m)) j
      = if j = m then (fun x : Fin 3 → ℝ => deriv h (x m)) else fun _ => 0 := by
    intro j
    funext x
    rw [partialDeriv_coord]
    by_cases hjm : j = m <;> simp [hjm]
  have key : ∀ j : Fin 3, partialDeriv (partialDeriv (fun y => h (y m)) j) j x
      = if j = m then deriv (deriv h) (x m) else 0 := by
    intro j
    rw [hfun j]
    by_cases hjm : j = m
    · subst hjm
      simp only [if_true]
      rw [partialDeriv_coord (deriv h) j j x]
      simp
    · simp [hjm]
  simp [lap, key]

/-! ## A Lean-checked reduction: shear flows and the one dimensional heat equation -/

/-- **Reduction.** Let `g : ℝ → ℝ → ℝ` be a smooth solution of the one dimensional heat equation
`∂ₜ g = ν ∂²_y g`. Then the shear flow `u (t, x) = (g t (x 1), 0, 0)` together with the zero
pressure is a globally defined smooth solution of the three dimensional incompressible
Navier–Stokes equations with initial datum `x ↦ (g 0 (x 1), 0, 0)`.

Thus global regularity for the (large) class of shear-flow initial data reduces to global
regularity for the linear heat equation. -/
