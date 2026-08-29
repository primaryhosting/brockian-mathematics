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

theorem navier_stokes_regularity_rest_state (ν : ℝ) :
    ∃ (u : ℝ → Vec → Vec) (p : ℝ → Vec → ℝ),
      IsGlobalSmoothSolution ν u p ∧ ∀ x, u 0 x = 0 := by
  obtain ⟨u, p, hsol, hinit⟩ := navier_stokes_regularity ν (fun _ => 0) contDiff_const
  exact ⟨u, p, hsol, hinit⟩

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

