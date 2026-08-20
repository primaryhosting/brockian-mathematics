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

theorem wilsonPrime_of_brocard (n m : ℕ) (hp : Nat.Prime (n + 1)) (h : n ! + 1 = m ^ 2) :
    (n + 1) ^ 2 ∣ n ! + 1 := by
  have hd := dvd_factorial_succ_of_prime_succ n hp
  rw [h] at hd ⊢
  exact pow_dvd_pow_of_dvd (hp.dvd_of_dvd_pow hd) 2

/-- Unconditional verification: for `8 ≤ n ≤ 100`, `n! + 1` is not a perfect square. -/
