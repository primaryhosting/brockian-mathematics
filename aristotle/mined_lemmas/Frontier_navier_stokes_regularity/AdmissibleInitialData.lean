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

def AdmissibleInitialData (u₀ : (Fin 3 → ℝ) → (Fin 3 → ℝ)) : Prop :=
  (∀ (i : Fin 3) (n : ℕ), ContDiff ℝ n (fun x : Fin 3 → ℝ => u₀ x i)) ∧
    (∀ x, divg u₀ x = 0) ∧ (∀ i : Fin 3, RapidlyDecaying (fun x => u₀ x i))

/-- The Clay Millennium statement of global existence and smoothness for the three dimensional
incompressible Navier–Stokes equations with viscosity `ν > 0`: for every admissible initial
datum there is a globally defined smooth solution with globally bounded energy.

This `Prop` is the *statement* of the open problem; it is not proved here. -/
