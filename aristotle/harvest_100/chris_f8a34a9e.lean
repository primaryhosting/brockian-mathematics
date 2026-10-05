/-
# Gram 5 Nonneg
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Weil.gram5_nonneg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option autoImplicit false

/-!
# Gram 5 Nonneg
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Weil.gram5_nonneg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann.Weil

/-- The quadratic form of the 5×5 positive semidefinite Gram matrix with `2` on the
diagonal and `1` off the diagonal is nonnegative:
`0 ≤ (x₀+x₁+x₂+x₃+x₄)² + (x₀²+x₁²+x₂²+x₃²+x₄²)`.

(The header block appears twice: Lean requires `import` to precede any module
docstring, so the mandated header is repeated as a plain comment at the very top
of the file.) -/
theorem gram5_nonneg (x0 x1 x2 x3 x4 : ℝ) :
    0 ≤ (x0 + x1 + x2 + x3 + x4) ^ 2 + (x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2) := by
  positivity

end Riemann.Weil

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

