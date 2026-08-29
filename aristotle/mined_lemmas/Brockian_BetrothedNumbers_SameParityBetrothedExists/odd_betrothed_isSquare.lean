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

theorem odd_betrothed_isSquare {m n : ℕ} (hb : Betrothed m n)
    (hm : Odd m) (hn : Odd n) : (∃ a, m = a ^ 2) ∧ (∃ b, n = b ^ 2) := by
  have hpar : m % 2 = n % 2 := by
    rw [Nat.odd_iff] at hm hn; omega
  obtain ⟨⟨a, hA⟩, ⟨b, hB⟩⟩ := squareType_of_betrothed_sameParity hb hpar
  rw [Nat.odd_iff] at hm hn
  refine ⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩
  · rcases hA with hA | hA
    · exact hA
    · omega
  · rcases hB with hB | hB
    · exact hB
    · omega

end Brockian.BetrothedNumbers

