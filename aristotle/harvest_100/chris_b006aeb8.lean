import Mathlib

/-!
# Gram 5 Nonneg
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Weil.gram5_nonneg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` lines to precede every other command, including
-- module docstrings, so the required header comment appears directly after the import.

set_option autoImplicit false

namespace Riemann.Weil

/-- The quadratic form of the 5×5 positive semidefinite Gram matrix with `2` on the
diagonal and `1` off the diagonal is nonnegative: it equals
`(x0+x1+x2+x3+x4)^2 + (x0^2+x1^2+x2^2+x3^2+x4^2)`, a sum of squares.

The proof is immediate from `even_two.pow_nonneg`-style facts (`sq_nonneg`) plus
`add_nonneg`; `positivity` assembles these automatically. -/
theorem gram5_nonneg (x0 x1 x2 x3 x4 : ℝ) :
    0 ≤ (x0 + x1 + x2 + x3 + x4) ^ 2 + (x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2) := by
  positivity

/-- Explicit `Mathlib`-lemma proof of the same fact, using only `sq_nonneg`
(`Mathlib.Algebra.Order.Ring.Lemmas`) and `add_nonneg`. -/
example (x0 x1 x2 x3 x4 : ℝ) :
    0 ≤ (x0 + x1 + x2 + x3 + x4) ^ 2 + (x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2) :=
  add_nonneg (sq_nonneg _)
    (add_nonneg (add_nonneg (add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))
      (sq_nonneg _)) (sq_nonneg _)) (sq_nonneg _))

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

