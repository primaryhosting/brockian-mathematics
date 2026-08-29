import Mathlib
/-!
# Lagrange Four Squares
Category: Pure Mathematics
Target: Math.lagrange_four_squares
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- NOTE: Lean 4 requires `import` commands to precede every other command, including
-- module doc comments (`/-! ... -/`). The requested header is therefore placed
-- immediately after the single `import Mathlib` line, which is the earliest legal
-- position for it in a compiling Lean file.

namespace Math

/-- **Lagrange's four squares theorem**: every natural number `n` can be written as
`a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2` for natural numbers `a b c d`.

The result is available in Mathlib as `Nat.sum_four_squares`
(`Mathlib/NumberTheory/SumFourSquares.lean`). -/
theorem lagrange_four_squares (n : ℕ) :
    ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n :=
  Nat.sum_four_squares n

end Math

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

