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

theorem modulus_reverse (x₁ x₂ x₃ x₄ : ℝ) :
    modulus x₄ x₃ x₂ x₁ = modulus x₁ x₂ x₃ x₄ := by
  unfold modulus
  rw [show (x₂ - x₄) * (x₁ - x₃) = (x₃ - x₁) * (x₄ - x₂) by ring,
    show (x₂ - x₃) * (x₁ - x₄) = (x₃ - x₂) * (x₄ - x₁) by ring]

/-- **Percolation form of the statement.**  Suppose the crossing probabilities `P n` of
critical percolation at mesh `1/n` on a quad with marked boundary points converge to a
limit `C`, and that (Smirnov's theorem) the limit `C` is conformally invariant.  Then the
limiting crossing probability depends only on the conformal modulus of the quad: two quads
of equal modulus have the same limiting crossing probability. -/
