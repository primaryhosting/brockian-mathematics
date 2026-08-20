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

theorem chain_step {n k : ℕ} (hnk : n ^ 2 < k ^ 3) (q p : ℕ) (hp : p.Prime)
    (hgap : (p - q - 1) ^ 3 ≤ q ^ 2) (H : n < q → ∃ r, r.Prime ∧ n < r ∧ r ≤ n + k) :
    n < p → ∃ r, r.Prime ∧ n < r ∧ r ≤ n + k := by
  intro hn
  rcases Nat.lt_or_ge n q with hq | hq
  · exact H hq
  · refine ⟨p, hp, hn, ?_⟩
    by_contra hc
    rw [not_le] at hc
    have hk : k ≤ p - q - 1 := by omega
    have h1 : k ^ 3 ≤ (p - q - 1) ^ 3 := Nat.pow_le_pow_left hk 3
    have h2 : q ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hq 2
    exact absurd hnk (by linarith)

set_option maxHeartbeats 1000000 in
/-- For `n` in the range covered by our chain of primes and `k ≥ n ^ (2/3)`,
the interval `(n, n+k]` contains a prime. -/
