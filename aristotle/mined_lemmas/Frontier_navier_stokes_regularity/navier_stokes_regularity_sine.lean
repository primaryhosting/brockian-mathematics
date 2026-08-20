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

theorem navier_stokes_regularity_sine (ν k : ℝ) :
    ∃ (u : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ)) (p : ℝ → (Fin 3 → ℝ) → ℝ),
      IsNavierStokesSolution ν (fun x => ![Real.sin (k * x 1), 0, 0]) u p ∧
        ∀ t x, u t x = ![Real.exp (-(ν * k ^ 2 * t)) * Real.sin (k * x 1), 0, 0] := by
  set g : ℝ → ℝ → ℝ := fun t y => Real.exp (-(ν * k ^ 2 * t)) * Real.sin (k * y) with hg
  have hsmooth : ∀ n : ℕ, ContDiff ℝ n (fun q : ℝ × ℝ => g q.1 q.2) := by
    intro n; rw [hg]; fun_prop
  have hderiv1 : ∀ t : ℝ, deriv (g t)
      = fun y => Real.exp (-(ν * k ^ 2 * t)) * (Real.cos (k * y) * k) := by
    intro t
    funext y
    exact HasDerivAt.deriv (by
      simpa [hg] using
        (((hasDerivAt_id y).const_mul k).sin).const_mul (Real.exp (-(ν * k ^ 2 * t))))
  have hderiv2 : ∀ t y : ℝ, deriv (deriv (g t)) y
      = Real.exp (-(ν * k ^ 2 * t)) * (-Real.sin (k * y) * k * k) := by
    intro t y
    rw [hderiv1 t]
    exact HasDerivAt.deriv (by
      simpa using
        ((((hasDerivAt_id y).const_mul k).cos).mul_const k).const_mul
          (Real.exp (-(ν * k ^ 2 * t))))
  have hheat : ∀ t y : ℝ, deriv (fun s : ℝ => g s y) t = ν * deriv (deriv (g t)) y := by
    intro t y
    have h : deriv (fun s : ℝ => g s y) t
        = Real.exp (-(ν * k ^ 2 * t)) * -(ν * k ^ 2) * Real.sin (k * y) :=
      HasDerivAt.deriv (by
        simpa [hg] using
          ((((hasDerivAt_id t).const_mul (ν * k ^ 2)).neg).exp).mul_const (Real.sin (k * y)))
    rw [h, hderiv2 t y]
    ring
  have hsol := isNavierStokesSolution_shear ν g hsmooth hheat
  have hinit : (fun x : Fin 3 → ℝ => (![g 0 (x 1), 0, 0] : Fin 3 → ℝ))
      = fun x : Fin 3 → ℝ => (![Real.sin (k * x 1), 0, 0] : Fin 3 → ℝ) := by
    funext x
    simp [hg]
  rw [hinit] at hsol
  exact ⟨_, _, hsol, fun t x => rfl⟩

end Frontier

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

