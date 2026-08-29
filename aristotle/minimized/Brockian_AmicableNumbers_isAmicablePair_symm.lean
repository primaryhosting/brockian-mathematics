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
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.AmicableNumbers

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- The sum of all (positive) divisors of `n`.  For `n = 0` this is `0`. -/

def sumOfDivisors (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- `m` and `n` form an *amicable pair*: they are distinct and each one's divisor sum
equals `m + n`.  Equivalently, the sum of the proper divisors of `m` is `n` and the sum
of the proper divisors of `n` is `m`. -/

def IsAmicablePair (m n : ℕ) : Prop :=
  m ≠ n ∧ sumOfDivisors m = m + n ∧ sumOfDivisors n = m + n

/-- The set of amicable numbers: those belonging to some amicable pair. -/

def AmicableSet : Set ℕ := {m | ∃ n, IsAmicablePair m n}

/-- Being an amicable pair is a symmetric relation. -/

theorem isAmicablePair_symm {m n : ℕ} (h : IsAmicablePair m n) : IsAmicablePair n m := by
  obtain ⟨hne, hm, hn⟩ := h
  refine ⟨hne.symm, ?_, ?_⟩ <;> omega

/-- `(220, 284)` is an amicable pair, so `AmicableSet` is not empty. -/
