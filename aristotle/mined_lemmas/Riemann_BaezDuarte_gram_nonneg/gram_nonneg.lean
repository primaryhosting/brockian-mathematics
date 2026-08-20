/-
# Gram Nonneg
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.BaezDuarte.gram_nonneg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Riemann
namespace BaezDuarte

/-- **Gram nonnegativity (clean self-contained case).**

The Nyman–Beurling / Baez-Duarte distance is a sum of squares of the form
`‖a - b‖²`; the basic scalar instance of this is `0 ≤ a² - 2ab + b²`,
which is the Gram form of the pair of vectors `a, b` in `ℝ`.

The Mathlib lemma that essentially closes it is `sq_nonneg` (applied to `a - b`). -/

theorem gram_nonneg (a b : ℝ) : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2 := by
  have h : a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
  rw [h]
  exact sq_nonneg (a - b)

/-- **Gram nonnegativity, general form.**

In any real inner product space `V`, for any finite family of vectors
`v : Fin n → V` and coefficients `c : Fin n → ℝ`, the Gram quadratic form
`∑ i, ∑ j, c i * c j * ⟪v i, v j⟫` is nonnegative, since it equals
`‖∑ i, c i • v i‖²`. -/
