/-
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
Mathlib does not state the `abc` conjecture. The closest existing material is
`UniqueFactorizationMonoid.radical` (`Mathlib/RingTheory/Radical.lean`), a general radical
of an element of a UFM, and the Mason–Stothers theorem
(`Mathlib/NumberTheory/FLT/MasonStothers.lean`), the polynomial analogue of `abc`.
Neither closes the statement below, so the radical for `ℕ` and both formulations of the
conjecture are set up here from scratch.
-/

namespace Frontier

open scoped BigOperators

/-- The radical of a natural number: the product of its distinct prime factors.
By convention `rad 0 = rad 1 = 1`. -/

theorem abcTriples_zero_infinite : (abcTriples 0).Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ => ((1, 3 ^ 2 ^ (k + 1) - 1, 3 ^ 2 ^ (k + 1)) : ℕ × ℕ × ℕ))
  · intro k l hkl
    have h : (3 : ℕ) ^ 2 ^ (k + 1) = 3 ^ 2 ^ (l + 1) := congrArg (fun t => t.2.2) hkl
    have := Nat.pow_right_injective (by norm_num : 2 ≤ 3) h
    have := Nat.pow_right_injective (by norm_num : 2 ≤ 2) this
    omega
  · intro k
    exact mem_abcTriples_zero k

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

