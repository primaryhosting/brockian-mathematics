/-
# Smirnov Percolation
Category: Frontier — Fields Medal Work
Target: Frontier.smirnov_percolation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Smirnov Percolation
Category: Frontier — Fields Medal Work
Target: Frontier.smirnov_percolation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Frontier

/-- A real Möbius transformation `x ↦ (a x + b) / (c x + d)`.  These are exactly the
boundary values on `ℝ = ∂ℍ` of the conformal automorphisms of the upper half-plane. -/

theorem conformallyInvariant_comp_modulus (F : ℝ → ℝ) :
    ConformallyInvariant (fun x₁ x₂ x₃ x₄ => F (modulus x₁ x₂ x₃ x₄)) :=
  (smirnov_percolation _).2 ⟨F, fun _ _ _ _ _ => rfl⟩

/-- The modulus is unchanged by reversing the cyclic order of the four marked points, as it
must be for a crossing probability between opposite sides of a quad. -/
