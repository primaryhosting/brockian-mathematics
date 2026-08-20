/-
# Gram Nonneg
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.BaezDuarte.gram_nonneg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators RealInnerProductSpace

namespace Riemann
namespace BaezDuarte

/-- The clean, self-contained Gram/distance nonnegativity statement:
for all real `a b`, `0 ≤ a^2 - 2*a*b + b^2`, i.e. the quadratic form is a square. -/

theorem gram_nonneg (a b : ℝ) : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2 := by
  have h : a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
  rw [h]
  positivity

/-- General finite Gram nonnegativity in a real inner product space: for any finite
family of vectors `v : Fin n → V` and coefficients `c : Fin n → ℝ`,
`0 ≤ ∑ i, ∑ j, c i * c j * ⟪v i, v j⟫`. -/
