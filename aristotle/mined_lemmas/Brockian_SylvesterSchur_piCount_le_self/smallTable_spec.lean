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

theorem smallTable_spec : ∀ e ∈ smallTable, 0 < e.1.1 → e.1.1 < e.1.2 →
    e.2.2 ∈ smallPrimes ∧ e.1.1 < e.2.2 ∧ e.2.1 < e.1.1 ∧
      e.2.2 ∣ (e.1.2 + 1 + e.2.1) := by
  decide +kernel

