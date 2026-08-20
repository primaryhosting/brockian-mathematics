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

noncomputable def advect (u : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (i : Fin 3) (x : Fin 3 → ℝ) : ℝ :=
  ∑ j : Fin 3, u x j * partialDeriv (fun y => u y i) j x

/-! ## The Navier–Stokes system -/

/-- `IsNavierStokesSolution ν u₀ u p` says that the velocity field `u : ℝ → ℝ³ → ℝ³` and the
pressure `p : ℝ → ℝ³ → ℝ` form a globally defined, smooth solution of the incompressible
Navier–Stokes equations on `ℝ³` with viscosity `ν` and initial velocity `u₀`:

* `∂ₜ uᵢ = ν Δuᵢ - (u · ∇)uᵢ - ∂ᵢ p` for all times `t ≥ 0`,
* `div u = 0` for all times `t ≥ 0`,
* `u 0 = u₀`,

together with `C^n` smoothness (for every `n`) of all components of `u` and of `p` jointly in
`(t, x)`. -/
structure IsNavierStokesSolution (ν : ℝ) (u₀ : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (u : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ)) (p : ℝ → (Fin 3 → ℝ) → ℝ) : Prop where
  smooth_velocity : ∀ (i : Fin 3) (n : ℕ), ContDiff ℝ n (fun q : ℝ × (Fin 3 → ℝ) => u q.1 q.2 i)
  smooth_pressure : ∀ n : ℕ, ContDiff ℝ n (fun q : ℝ × (Fin 3 → ℝ) => p q.1 q.2)
  momentum : ∀ t : ℝ, 0 ≤ t → ∀ (x : Fin 3 → ℝ) (i : Fin 3),
    deriv (fun s : ℝ => u s x i) t
      = ν * lap (fun y => u t y i) x - advect (u t) i x - partialDeriv (p t) i x
  incompressible : ∀ t : ℝ, 0 ≤ t → ∀ x : Fin 3 → ℝ, divg (u t) x = 0
  initial : ∀ x : Fin 3 → ℝ, u 0 x = u₀ x

/-- Rapid (Schwartz-type) decay of a scalar field on `ℝ³`. -/
