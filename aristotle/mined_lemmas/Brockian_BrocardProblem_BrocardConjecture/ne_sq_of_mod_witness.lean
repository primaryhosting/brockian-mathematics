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

import Mathlib
import Brockian.BrocardProblem

/-!
# Brocard's problem, in Mathlib's vocabulary

`Brockian/BrocardProblem.lean` is import-free (so that the required header
comment can be its first line), and therefore defines factorial itself as
`Brockian.BrocardProblem.fact`.  Here we check that `fact` agrees with Mathlib's
`Nat.factorial` and restate the two main results using `Nat.factorial`.
-/

namespace Brockian.BrocardProblem

open Nat

/-- The self-contained factorial of `Brockian/BrocardProblem.lean` agrees with
Mathlib's `Nat.factorial`. -/

theorem ne_sq_of_mod_witness {a p : Nat} (hp : 0 < p)
    (h : ∀ x < p, x * x % p ≠ a % p) (m : Nat) : a ≠ m ^ 2 := by
  rintro rfl
  refine h (m % p) (Nat.mod_lt _ hp) ?_
  rw [← Nat.mul_mod]
  simp [Nat.pow_succ]

/-- A certificate for `n` rules out every solution of `n ! + 1 = m ^ 2`. -/
