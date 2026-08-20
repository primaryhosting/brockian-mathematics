import Mathlib
namespace Brockian.SylvesterSchur

/-!
# The Sylvester–Schur theorem

If `n > k ≥ 1` then one of `n+1, …, n+k` has a prime factor `> k`.

The proof follows Erdős' argument: assuming the contrary, every prime factor of the
binomial coefficient `(n+k).choose k` is at most `k`.  This yields two upper bounds for
that binomial coefficient (one via the number of primes `≤ k`, one via the primorial),
both of which are contradicted by an elementary lower bound, except in a range of small
parameters which is covered by an explicit chain of primes.
-/

open Finset Real

/-! ### An elementary upper bound for the prime counting function -/

/-- The number of primes `≤ k`. -/

theorem smallPrimes_prime : ∀ p ∈ smallPrimes, Nat.Prime p := by decide

set_option maxRecDepth 100000 in
/-- For each pair `(k, n)` with `k < 26` and `n < 200`, an explicit witness `(i, p)`:
`p` is a prime larger than `k` dividing `n + 1 + i`, and `i < k`.  (For the irrelevant
pairs, those with `k = 0` or `n ≤ k`, the entry is `(0, 0)`.) -/
