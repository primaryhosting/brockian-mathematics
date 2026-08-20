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
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BetrothedNumbers

open Finset

/-- `sigmaOne n` is the sum of all positive divisors of `n`. -/

def sigmaOne (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- A pair `(m, n)` is *betrothed* (a *quasi-amicable pair*) when `m` and `n` are distinct
positive integers such that the sum of the divisors of each, excluding `1` and the number
itself, equals the other number.  Equivalently `σ m = σ n = m + n + 1`. -/

def IsBetrothed (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ sigmaOne m = m + n + 1 ∧ sigmaOne n = m + n + 1

/-- The set of betrothed pairs. -/

theorem isBetrothed_48_75 : IsBetrothed 48 75 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;> decide

/-- `(140, 195)` is a betrothed pair. -/

theorem IsBetrothed.right_unique {m n n' : ℕ} (h : IsBetrothed m n) (h' : IsBetrothed m n') :
    n = n' := by
  obtain ⟨-, -, -, h1, -⟩ := h
  obtain ⟨-, -, -, h2, -⟩ := h'
  omega

/-- The first-coordinate map is injective on the set of betrothed pairs. -/
