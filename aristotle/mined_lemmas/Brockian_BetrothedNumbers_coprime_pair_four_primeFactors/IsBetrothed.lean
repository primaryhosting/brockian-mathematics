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

def IsBetrothed (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ sigma 1 m = m + n + 1 ∧ sigma 1 n = m + n + 1

/-- The geometric-sum identity `(1 + p + ⋯ + p ^ k) * (p - 1) + 1 = p ^ (k + 1)`. -/
