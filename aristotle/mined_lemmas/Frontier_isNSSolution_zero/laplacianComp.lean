/-
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open scoped BigOperators

/-- Physical space `ℝ³`. -/
abbrev Vec := EuclideanSpace ℝ (Fin 3)

/-- The `i`-th partial derivative of a scalar field on `ℝ³`. -/

noncomputable def laplacianComp (u : ℝ → Vec → Vec) (t : ℝ) (i : Fin 3) (x : Vec) : ℝ :=
  ∑ j, pd j (fun y => pd j (fun z => u t z i) y) x

/-- `IsNSSolution ν u p u₀` says that the pair `(u, p)` is a globally defined, smooth
solution of the incompressible Navier–Stokes equations on `ℝ³ × ℝ` with viscosity `ν`,
no external force, and initial velocity `u₀`:

* `u` and `p` are `C^∞` jointly in time and space,
* `u 0 = u₀`,
* `div u = 0` (incompressibility),
* `∂ₜ uᵢ + ∑ⱼ uⱼ ∂ⱼ uᵢ = ν Δuᵢ - ∂ᵢ p` (conservation of momentum). -/
structure IsNSSolution (nu : ℝ) (u : ℝ → Vec → Vec) (p : ℝ → Vec → ℝ) (u₀ : Vec → Vec) :
    Prop where
  smooth_velocity : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × Vec => u q.1 q.2)
  smooth_pressure : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × Vec => p q.1 q.2)
  initial_condition : ∀ x, u 0 x = u₀ x
  incompressible : ∀ t x, divergence (u t) x = 0
  momentum : ∀ t x i,
    deriv (fun s => u s x i) t + ∑ j, u t x j * pd j (fun y => u t y i) x
      = nu * laplacianComp u t i x - pd i (p t) x

/-- **Global regularity for the three dimensional incompressible Navier–Stokes equations.**

For every positive viscosity and every smooth, divergence free initial velocity field there
exists a globally defined smooth solution of the Navier–Stokes equations with that initial
datum.  This is the (unsolved) Clay Millennium Problem statement; it is *stated* here, not
assumed anywhere. -/
