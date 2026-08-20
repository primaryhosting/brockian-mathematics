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

/-- The sum-of-divisors function `σ₁ n = ∑_{d ∣ n} d`. -/

theorem isBetrothedPair_iff_sum_properDivisors {m n : ℕ} :
    IsBetrothedPair m n ↔
      0 < m ∧ 0 < n ∧ m ≠ n ∧
        (∑ d ∈ m.properDivisors, d) = n + 1 ∧ (∑ d ∈ n.properDivisors, d) = m + 1 := by
  have hm : sigmaOne m = (∑ d ∈ m.properDivisors, d) + m :=
    Nat.sum_divisors_eq_sum_properDivisors_add_self
  have hn : sigmaOne n = (∑ d ∈ n.properDivisors, d) + n :=
    Nat.sum_divisors_eq_sum_properDivisors_add_self
  unfold IsBetrothedPair
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨h1, h2, h3, by omega, by omega⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨h1, h2, h3, by omega, by omega⟩

/-- The sum of divisors of a prime `p` is `p + 1`. -/
