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

/-
# Brocard Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardProblem.BrocardConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to be the first command in a file, so the header above is a
-- plain block comment rather than a module docstring.)

import Mathlib

set_option maxRecDepth 40000

namespace Brockian.BrocardProblem

open Nat

/-- `IsBrocardSolution n m` says that `(n, m)` solves Brocard's equation `n! + 1 = m²`. -/

theorem not_square_of_between {N k : ℕ} (h1 : k ^ 2 < N) (h2 : N < (k + 1) ^ 2) :
    ¬ ∃ m : ℕ, N = m ^ 2 := by
  rintro ⟨m, rfl⟩
  have hk : k < m := by nlinarith
  have hm : m < k + 1 := by nlinarith
  omega

/-!
## An equivalent form of Brocard's equation

For `n ≥ 2`, `n! + 1` is a square exactly when `n!/4` is a product of two consecutive
integers.  This is the standard reformulation `n! = (m-1)(m+1)` with `m` odd.
-/

/-- Reformulation of Brocard's equation: for `n ≥ 2`, `n! + 1` is a perfect square iff
`n!` is four times a product of two consecutive integers. -/
