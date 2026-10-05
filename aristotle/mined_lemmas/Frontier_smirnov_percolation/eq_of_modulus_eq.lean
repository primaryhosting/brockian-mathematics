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

theorem eq_of_modulus_eq {C : ℝ → ℝ → ℝ → ℝ → ℝ} (hC : ConformallyInvariant C)
    {x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : ℝ}
    (hx : Distinct4 x₁ x₂ x₃ x₄) (hy : Distinct4 y₁ y₂ y₃ y₄)
    (h : modulus x₁ x₂ x₃ x₄ = modulus y₁ y₂ y₃ y₄) :
    C x₁ x₂ x₃ x₄ = C y₁ y₂ y₃ y₄ := by
  obtain ⟨a, b, c, d, hdet, h1, h2, h3, h4, e1, e2, e3, e4⟩ :=
    exists_mobius_of_modulus_eq hx hy h
  have := hC a b c d x₁ x₂ x₃ x₄ hdet hx h1 h2 h3 h4
  rw [e1, e2, e3, e4] at this
  exact this.symm

/-- The induced function of the modulus: it picks, for each possible value `l` of the
conformal modulus, the value of `C` on some quad with that modulus.  For a conformally
invariant `C` this is well defined, and it is the abstract "Cardy function" of `C`. -/
