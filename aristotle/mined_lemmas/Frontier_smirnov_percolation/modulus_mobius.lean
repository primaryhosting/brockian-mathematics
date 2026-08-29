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

theorem modulus_mobius {a b c d x₁ x₂ x₃ x₄ : ℝ} (hdet : a * d - b * c ≠ 0)
    (hx : Distinct4 x₁ x₂ x₃ x₄)
    (h1 : c * x₁ + d ≠ 0) (h2 : c * x₂ + d ≠ 0) (h3 : c * x₃ + d ≠ 0) (h4 : c * x₄ + d ≠ 0) :
    modulus (mobius a b c d x₁) (mobius a b c d x₂) (mobius a b c d x₃) (mobius a b c d x₄)
      = modulus x₁ x₂ x₃ x₄ := by
  obtain ⟨a12, a13, a14, a23, a24, a34⟩ := hx
  have e31 : x₃ - x₁ ≠ 0 := sub_ne_zero.2 (Ne.symm a13)
  have e42 : x₄ - x₂ ≠ 0 := sub_ne_zero.2 (Ne.symm a24)
  have e32 : x₃ - x₂ ≠ 0 := sub_ne_zero.2 (Ne.symm a23)
  have e41 : x₄ - x₁ ≠ 0 := sub_ne_zero.2 (Ne.symm a14)
  unfold modulus
  rw [mobius_sub h3 h1, mobius_sub h4 h2, mobius_sub h3 h2, mobius_sub h4 h1]
  field_simp

/-- The modulus determines a quad up to a Möbius transformation: given two quads with the
same modulus there is a Möbius map carrying the first onto the second. -/
