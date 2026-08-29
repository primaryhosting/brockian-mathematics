import Mathlib
-- (Lean 4 requires `import` lines to precede every other token, including module
-- doc-comments, so the required header comment appears immediately below.)

/-!
# Lagrange Four Squares
Category: Pure Mathematics
Target: Math.lagrange_four_squares
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Math

/-- **Lagrange's four-square theorem**: every natural number `n` can be written as
`a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2` for natural numbers `a`, `b`, `c`, `d`. -/
theorem lagrange_four_squares (n : ℕ) :
    ∃ a b c d : ℕ, n = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares n
  exact ⟨a, b, c, d, h.symm⟩

/-- The integer form of Lagrange's four-square theorem: every nonnegative integer is a sum
of four squares of integers. -/
theorem lagrange_four_squares_int {n : ℤ} (hn : 0 ≤ n) :
    ∃ a b c d : ℤ, n = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  lift n to ℕ using hn with m
  obtain ⟨a, b, c, d, h⟩ := lagrange_four_squares m
  exact ⟨a, b, c, d, by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) h⟩

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

