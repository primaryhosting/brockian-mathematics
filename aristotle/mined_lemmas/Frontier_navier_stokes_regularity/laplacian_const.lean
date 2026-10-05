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

@[simp] lemma laplacian_const (c : ℝ) (x : Vec) :
    laplacian (fun _ : Vec => c) x = 0 := by
  have h : ∀ j, partialDeriv (fun _ : Vec => c) j = fun _ : Vec => (0 : ℝ) := by
    intro j; funext y; exact partialDeriv_const c j y
  simp [laplacian, h]

/-- The gradient of the linear pressure `x ↦ -⟨c, x⟩`. -/
