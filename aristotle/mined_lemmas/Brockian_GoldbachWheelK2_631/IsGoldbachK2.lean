import Mathlib

/-!
# Goldbach Wheel K 2 631
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_631
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-- `IsGoldbachK2 n` : `n` is a sum of `K = 2` primes. -/

def IsGoldbachK2 (n : ℕ) : Prop := ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n

/-- The wheel-spoke core of the verification, in the equivalent bounded/decidable form:
for every even `n` in the window `[4, 631]` there is a prime `p < 48` (a spoke of the
wheel) with `n - p` prime. -/
