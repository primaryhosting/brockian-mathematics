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

noncomputable def modulus (x₁ x₂ x₃ x₄ : ℝ) : ℝ :=
  ((x₃ - x₁) * (x₄ - x₂)) / ((x₃ - x₂) * (x₄ - x₁))

/-- A crossing-probability function `C` on quads is *conformally invariant* if it is
unchanged by every Möbius transformation of the half-plane (applied to the four marked
boundary points).  This is the Cardy–Smirnov conformal invariance property. -/
