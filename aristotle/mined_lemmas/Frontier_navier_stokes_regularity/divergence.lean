/-
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open ContDiff

namespace Frontier

/-- The physical space `ℝ³`, modelled as `Fin 3 → ℝ`. -/
abbrev Vec := Fin 3 → ℝ

/-- The `i`-th partial derivative of a scalar field on `ℝ³`. -/

noncomputable def divergence (v : Vec → Vec) (x : Vec) : ℝ :=
  ∑ i, partialDeriv (fun y => v y i) i x

/-- `u` (a time dependent velocity field) together with `p` (a time dependent pressure)
is a *global smooth solution* of the incompressible Navier–Stokes equations on `ℝ × ℝ³`
with viscosity `ν`:

* `u` and `p` are `C^∞` jointly in time and space;
* `u` is divergence free (incompressibility);
* the momentum equation `∂ₜuᵢ + (u · ∇)uᵢ = ν Δuᵢ - ∂ᵢp` holds at every point of
  space-time.
-/
structure IsGlobalSmoothSolution (ν : ℝ) (u : ℝ → Vec → Vec) (p : ℝ → Vec → ℝ) : Prop where
  smooth_velocity : ContDiff ℝ ∞ (fun q : ℝ × Vec => u q.1 q.2)
  smooth_pressure : ContDiff ℝ ∞ (fun q : ℝ × Vec => p q.1 q.2)
  incompressible : ∀ t x, divergence (u t) x = 0
  momentum : ∀ t x i,
    deriv (fun s => u s x i) t + ∑ j, u t x j * partialDeriv (fun y => u t y i) j x
      = ν * laplacian (fun y => u t y i) x - partialDeriv (p t) i x

/-- **Global regularity for the 3D incompressible Navier–Stokes equations** (the Clay
Millennium Problem, here in its whole–space, force–free formulation): for every smooth,
divergence-free initial velocity field `u₀` on `ℝ³` there exist a globally defined smooth
velocity field `u` and pressure `p` solving the Navier–Stokes equations with viscosity `ν`
and with initial datum `u₀`.

This `Prop` is the *statement* of the open problem; it is not asserted here.  The theorem
`Frontier.navier_stokes_regularity` below proves an unconditional special case of it. -/
