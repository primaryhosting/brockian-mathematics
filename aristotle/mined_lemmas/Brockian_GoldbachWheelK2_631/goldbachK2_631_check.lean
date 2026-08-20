/-
# Goldbach Wheel K 2 631
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_631
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Wheel K 2 631
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_631
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Brockian

/-- The `K = 2` Goldbach property: `n` is a sum of two prime numbers. -/

private lemma goldbachK2_631_check :
    ∀ n ∈ Finset.range 632, 4 ≤ n → n % 2 = 0 →
      ∃ p ∈ Finset.range 632, Nat.Prime p ∧ Nat.Prime (n - p) := by
  decide

/-- **Goldbach wheel, `K = 2`, modulus `631`.**
Every even number `n` with `4 ≤ n ≤ 631` is a sum of two primes. -/
