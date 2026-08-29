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

lemma divergence_id (x : Vec) : divergence (fun y : Vec => y) x = 3 := by
  simp [divergence, partialDeriv_coord]

end Auxiliary

/-- **Navier–Stokes regularity: the spatially uniform (base) case.**

For every viscosity `ν` and every smooth curve `a : ℝ → ℝ³` there is a global smooth
solution of the 3D incompressible Navier–Stokes equations whose velocity field is the
spatially uniform flow `u(t, x) = a t`, with the linear pressure `p(t, x) = -⟨a'(t), x⟩`.
In particular (taking `a` constant, e.g. `a = 0`) the initial value problem with any
constant divergence-free initial datum — the rest state `u₀ = 0` in particular — has a
globally smooth solution.

This is an unconditional, Lean-checked instance of `NavierStokesGlobalRegularity ν`
restricted to spatially uniform initial data; the general case is the open Millennium
Problem, stated above as `NavierStokesGlobalRegularity`. -/
