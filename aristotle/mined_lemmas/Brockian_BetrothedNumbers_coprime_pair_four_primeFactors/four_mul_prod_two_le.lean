/-
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian.BetrothedNumbers

open ArithmeticFunction

/-- `m` and `n` form a *betrothed* (quasi-amicable) pair: both are positive, distinct, and
the sum of the divisors of each equals `m + n + 1`. -/

lemma four_mul_prod_two_le {a b : ℕ} (ha : a.Prime) (hab : a < b) :
    4 * (a * b) ≤ 15 * ((a - 1) * (b - 1)) := by
  have ha2 : 2 ≤ a := ha.two_le
  have hb3 : 3 ≤ b := by omega
  obtain ⟨x, rfl⟩ : ∃ x, a = x + 2 := ⟨a - 2, by omega⟩
  obtain ⟨y, rfl⟩ : ∃ y, b = y + 3 := ⟨b - 3, by omega⟩
  have e1 : x + 2 - 1 = x + 1 := by omega
  have e2 : y + 3 - 1 = y + 2 := by omega
  rw [e1, e2]
  nlinarith [Nat.zero_le x, Nat.zero_le y, Nat.zero_le (x * y)]

/-- Symmetric version of `four_mul_prod_two_le`. -/
