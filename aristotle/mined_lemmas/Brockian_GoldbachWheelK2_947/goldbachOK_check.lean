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

lemma goldbachOK_check :
    (List.range' 4 1891).all (fun n => (n % 2 == 1) || goldbachOK n) = true := by decide

/-- **Goldbach wheel, `K = 2`, modulus `947`.**  Every even `n` with `4 ≤ n ≤ 2 * 947`
is a sum of two primes `p + q` with `p ≤ q`. -/
