/-
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open scoped Real

/-- The radical of a natural number: the product of its distinct prime divisors. -/

theorem abc_exceptional_zero_infinite : (exceptionalSet 0).Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ => ((1, 9 ^ (k + 1) - 1, 9 ^ (k + 1)) : ℕ × ℕ × ℕ))
  · intro i j hij
    have h : (9 : ℕ) ^ (i + 1) = 9 ^ (j + 1) := congrArg (fun p => p.2.2) hij
    have := Nat.pow_right_injective (by norm_num : 2 ≤ 9) h
    omega
  · intro k
    exact nine_pow_triple_mem_exceptional (Nat.le_add_left 1 k)

end Frontier

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

