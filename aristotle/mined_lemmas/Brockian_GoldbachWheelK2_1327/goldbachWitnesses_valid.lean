import Mathlib

/-!
# Goldbach Wheel K 2 1327
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1327
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires all `import` commands to come before any other command,
-- including module docstrings, so `import Mathlib` precedes the header above.

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 40000

namespace Brockian

/-- A kernel-friendly primality certificate: `n` has no divisor `d` with
`2 ≤ d ≤ 52` and `d * d ≤ n`.  For `n < 53 ^ 2 = 2809` this is equivalent to
primality of `n` (given `2 ≤ n`). -/

theorem goldbachWitnesses_valid :
    goldbachWitnesses.all
      (fun x => decide (2 ≤ x.2) && decide (2 * x.2 ≤ x.1) && decide (x.1 ≤ 2654)
        && primeCert x.2 && primeCert (x.1 - x.2)) = true := by
  decide

/-- **Goldbach wheel, K = 2, modulus 1327.**
Every even number `n` with `4 ≤ n ≤ 2 * 1327` is the sum of two primes `p ≤ q`. -/
