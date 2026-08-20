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

theorem isBetrothed_iff {m n : ℕ} :
    IsBetrothed m n ↔
      0 < m ∧ 0 < n ∧ m ≠ n ∧ betrothedPartner m = n ∧ betrothedPartner n = m := by
  unfold IsBetrothed betrothedPartner
  constructor
  · rintro ⟨hm, hn, hmn, h1, h2⟩
    exact ⟨hm, hn, hmn, by omega, by omega⟩
  · rintro ⟨hm, hn, hmn, h1, h2⟩
    exact ⟨hm, hn, hmn, by omega, by omega⟩

/-- The set of numbers that belong to some betrothed pair as the first member. -/
