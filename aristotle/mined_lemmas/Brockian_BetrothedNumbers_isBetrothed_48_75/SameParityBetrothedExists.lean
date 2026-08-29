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

open Finset ArithmeticFunction

namespace Brockian.BetrothedNumbers

/-- `IsBetrothed m n` says that `(m, n)` is a *betrothed* (quasi-amicable) pair:
two distinct positive integers each of whose sum of *proper* divisors is one more
than the other, i.e. `σ m = σ n = m + n + 1`. -/

theorem SameParityBetrothedExists :
    (∃ m n : ℕ, IsBetrothed m n ∧ m % 2 = n % 2) ↔
      (∃ m n : ℕ, IsBetrothed m n ∧ (∃ a, m = a ^ 2 ∨ m = 2 * a ^ 2) ∧
        (∃ b, n = b ^ 2 ∨ n = 2 * b ^ 2)) := by
  constructor
  · rintro ⟨m, n, hb, hpar⟩
    obtain ⟨h1, h2⟩ := (sameParity_iff_of_isBetrothed hb).mp hpar
    exact ⟨m, n, hb, h1, h2⟩
  · rintro ⟨m, n, hb, h1, h2⟩
    exact ⟨m, n, hb, (sameParity_iff_of_isBetrothed hb).mpr ⟨h1, h2⟩⟩

end Brockian.BetrothedNumbers

