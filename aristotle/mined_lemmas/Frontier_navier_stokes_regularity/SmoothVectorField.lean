import Mathlib
/-!
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ContDiff
open MeasureTheory

namespace Frontier

/-! ## Basic differential operators on `ℝ³` -/

/-- The physical space `ℝ³`, as functions `Fin 3 → ℝ`. -/
abbrev Vec := Fin 3 → ℝ

/-- The `i`-th partial derivative of a scalar field on `ℝ³`. -/

def SmoothVectorField (u : ℝ → Vec → Vec) : Prop :=
  ContDiff ℝ ∞ fun q : ℝ × Vec => u q.1 q.2

/-! ## The incompressible Navier–Stokes equations -/

/-- `IsNSSolution nu f u p` says that the velocity field `u` and pressure `p` solve the
incompressible Navier–Stokes equations on `ℝ × ℝ³` with viscosity `nu` and external force `f`:

* momentum:       `∂ₜuⱼ + ∑ᵢ uᵢ ∂ᵢ uⱼ = nu Δuⱼ - ∂ⱼ p + fⱼ`,
* incompressible: `∇ · u = 0`. -/
structure IsNSSolution (nu : ℝ) (f : ℝ → Vec → Vec) (u : ℝ → Vec → Vec)
    (p : ℝ → Vec → ℝ) : Prop where
  momentum : ∀ t x j, deriv (fun s => u s x j) t + convective (u t) x j
      = nu * laplacian (fun y => u t y j) x - partialD (p t) j x + f t x j
  incompressible : ∀ t x, divergence (u t) x = 0

/-- `GlobalRegular nu f u p` says that `(u, p)` is a globally defined, everywhere smooth
solution of the Navier–Stokes equations with viscosity `nu` and force `f`. -/
