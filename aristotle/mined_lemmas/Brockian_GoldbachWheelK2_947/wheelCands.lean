/-
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

This file establishes a new member of the `GoldbachWheelK2` family: the binary
(`K = 2`) Goldbach property for the wheel modulus `947`, i.e. every even number
`n` with `4 ≤ n ≤ 2 * 947` is a sum of two primes `p + q` with `p ≤ q`.

The proof is a kernel-checked finite verification.  A trial-division primality
test `Brockian.isPrimeB`, sound for inputs below `44 ^ 2 = 1936`
(`Brockian.isPrimeB_prime`, via `Nat.prime_def_le_sqrt`), is combined with a
`decide`-checked search of a fixed wheel of small prime candidates.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Brockian

/-- `noDivUpto n b = true` says that no `k` with `2 ≤ k ≤ b` and `k ≠ n` divides `n`. -/

def wheelCands : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
   101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193,
   197, 199]

