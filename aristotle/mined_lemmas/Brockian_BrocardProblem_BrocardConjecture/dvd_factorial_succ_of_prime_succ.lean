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

import Mathlib

namespace Brockian.BrocardProblem

open Nat

set_option maxRecDepth 100000

/-- The statement of Brocard's conjecture: the only natural numbers `n` for which
`n! + 1` is a perfect square are `n = 4`, `n = 5` and `n = 7`
(with `4! + 1 = 5²`, `5! + 1 = 11²`, `7! + 1 = 71²`). -/

theorem dvd_factorial_succ_of_prime_succ (n : ℕ) (hp : Nat.Prime (n + 1)) :
    (n + 1) ∣ n ! + 1 := by
  haveI : Fact (Nat.Prime (n + 1)) := ⟨hp⟩
  have hw := ZMod.wilsons_lemma (n + 1)
  simp only [Nat.add_sub_cancel] at hw
  have h0 : ((n ! + 1 : ℕ) : ZMod (n + 1)) = 0 := by push_cast [hw]; ring
  exact Fin.natCast_eq_zero.mp h0

/-- **Unconditional partial result (Wilson primes).**  If `n! + 1` is a perfect square and
`p = n + 1` is prime, then `p` is a *Wilson prime*, i.e. `p² ∣ (p-1)! + 1`.
Wilson primes are extremely rare (the only ones known are `5`, `13` and `563`), so this
rules out a solution at `n = p - 1` for every prime `p` that is not a Wilson prime. -/
