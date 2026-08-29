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

lemma four_mul_prod_two_le' {a b : ℕ} (ha : a.Prime) (hb : b.Prime) (hab : a ≠ b) :
    4 * (a * b) ≤ 15 * ((a - 1) * (b - 1)) := by
  rcases Nat.lt_or_ge a b with h | h
  · exact four_mul_prod_two_le ha h
  · have h : b < a := lt_of_le_of_ne h (Ne.symm hab)
    have hba := four_mul_prod_two_le hb h
    calc 4 * (a * b) = 4 * (b * a) := by ring
      _ ≤ 15 * ((b - 1) * (a - 1)) := hba
      _ = 15 * ((a - 1) * (b - 1)) := by ring

/-- Three increasing primes satisfy `4abc ≤ 15 (a-1)(b-1)(c-1)`; the extremal case is
`(a, b, c) = (2, 3, 5)`, where both sides equal `120`. -/
