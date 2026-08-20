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

def RapidlyDecaying (u₀ : Vec → Vec) : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, ∀ x : Vec, ‖u₀ x‖ ≤ C / (1 + ‖x‖) ^ N

/-- **The Navier–Stokes global regularity conjecture** (Clay Millennium Problem: existence
and smoothness on `ℝ³`): for every positive viscosity and every smooth, divergence-free,
rapidly decaying initial datum there exist a globally defined smooth velocity field and
pressure, with no external force, solving the Navier–Stokes equations, attaining the initial
datum, and having uniformly bounded kinetic energy.  This statement is open. -/
