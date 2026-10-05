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

theorem goldbachWheelK2_631_decidable_core :
    ∀ n ∈ Finset.range 632, 4 ≤ n → n % 2 = 0 →
      ∃ p ∈ Finset.range 48, Nat.Prime p ∧ Nat.Prime (n - p) ∧ p + (n - p) = n := by
  decide

/-- **Goldbach wheel, `K = 2`, modulus `631`.**
Every even natural number `n` with `4 ≤ n ≤ 631` is a sum of two primes; moreover a witness
can always be taken with the smaller prime below `48`. -/
