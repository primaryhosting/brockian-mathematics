import Mathlib

/-!
# Gram 5 Nonneg
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Weil.gram5_nonneg
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Riemann
namespace Weil

/-- The quadratic form of the 5×5 PSD Gram matrix with `2` on the diagonal and `1`
off-diagonal is nonnegative: it is the sum of the square of the total sum and the
sum of the individual squares. -/
theorem gram5_nonneg (x0 x1 x2 x3 x4 : ℝ) :
    0 ≤ (x0 + x1 + x2 + x3 + x4) ^ 2 + (x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2) := by
  have h : (0:ℝ) ≤ (x0 + x1 + x2 + x3 + x4) ^ 2 := sq_nonneg _
  have h0 : (0:ℝ) ≤ x0 ^ 2 := sq_nonneg _
  have h1 : (0:ℝ) ≤ x1 ^ 2 := sq_nonneg _
  have h2 : (0:ℝ) ≤ x2 ^ 2 := sq_nonneg _
  have h3 : (0:ℝ) ≤ x3 ^ 2 := sq_nonneg _
  have h4 : (0:ℝ) ≤ x4 ^ 2 := sq_nonneg _
  linarith

end Weil
end Riemann

