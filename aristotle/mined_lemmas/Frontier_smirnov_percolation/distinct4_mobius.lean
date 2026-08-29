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

lemma distinct4_mobius {a b c d x₁ x₂ x₃ x₄ : ℝ} (hdet : a * d - b * c ≠ 0)
    (hx : Distinct4 x₁ x₂ x₃ x₄)
    (h1 : c * x₁ + d ≠ 0) (h2 : c * x₂ + d ≠ 0) (h3 : c * x₃ + d ≠ 0) (h4 : c * x₄ + d ≠ 0) :
    Distinct4 (mobius a b c d x₁) (mobius a b c d x₂) (mobius a b c d x₃)
      (mobius a b c d x₄) := by
  obtain ⟨a12, a13, a14, a23, a24, a34⟩ := hx
  exact ⟨mobius_ne hdet h1 h2 a12, mobius_ne hdet h1 h3 a13, mobius_ne hdet h1 h4 a14,
    mobius_ne hdet h2 h3 a23, mobius_ne hdet h2 h4 a24, mobius_ne hdet h3 h4 a34⟩

/-- **Conformal invariance of the modulus.**  The cross-ratio of four boundary points is
unchanged by Möbius transformations. -/
