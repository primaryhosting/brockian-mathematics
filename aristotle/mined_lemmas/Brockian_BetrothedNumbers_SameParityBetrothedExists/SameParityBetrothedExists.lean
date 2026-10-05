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
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.BetrothedNumbers

open ArithmeticFunction Finset

/-- `sigmaOne n` is the sum of all divisors of `n`. -/

theorem SameParityBetrothedExists :
    (∃ m n, Betrothed m n ∧ m % 2 = n % 2) ↔
      (∃ m n, Betrothed m n ∧ m % 2 = n % 2 ∧ SquareType m ∧ SquareType n) := by
  constructor
  · rintro ⟨m, n, hb, hpar⟩
    exact ⟨m, n, hb, hpar, (squareType_of_betrothed_sameParity hb hpar).1,
      (squareType_of_betrothed_sameParity hb hpar).2⟩
  · rintro ⟨m, n, hb, hpar, -, -⟩
    exact ⟨m, n, hb, hpar⟩

/-- If a betrothed pair of two odd numbers exists, both members are (odd) perfect squares. -/
