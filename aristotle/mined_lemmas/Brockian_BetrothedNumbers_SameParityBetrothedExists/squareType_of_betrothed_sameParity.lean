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

theorem squareType_of_betrothed_sameParity {m n : ℕ} (hb : Betrothed m n)
    (hpar : m % 2 = n % 2) : SquareType m ∧ SquareType n := by
  obtain ⟨hm, hn, -, hsm, hsn⟩ := hb
  have hodd : Odd (m + n + 1) := by rw [Nat.odd_iff]; omega
  exact ⟨squareType_of_odd_sigmaOne hm (hsm ▸ hodd),
    squareType_of_odd_sigmaOne hn (hsn ▸ hodd)⟩

/-- The classical smallest betrothed pair `(48, 75)`; it has *opposite* parity.
This witnesses that `Betrothed` is not vacuous. -/
