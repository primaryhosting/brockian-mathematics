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

theorem small_cases : ∀ k ∈ Finset.range 26, ∀ n ∈ Finset.range 200, 0 < k → k < n →
    ∃ i ∈ Finset.range k, ∃ p ∈ smallPrimes, k < p ∧ p ∣ (n + 1 + i) := by
  intro k hk n hn hk0 hkn
  have hmem : (k, n) ∈ smallTable.map Prod.fst := by
    rw [smallTable_keys]
    simp only [List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨k, Finset.mem_range.1 hk, n, Finset.mem_range.1 hn, rfl⟩
  obtain ⟨e, he, hek⟩ := List.mem_map.1 hmem
  have hk1 : e.1.1 = k := by rw [hek]
  have hk2 : e.1.2 = n := by rw [hek]
  obtain ⟨h1, h2, h3, h4⟩ :=
    smallTable_spec e he (by rw [hk1]; exact hk0) (by rw [hk1, hk2]; exact hkn)
  rw [hk1] at h2 h3
  rw [hk2] at h4
  exact ⟨e.2.1, Finset.mem_range.2 h3, e.2.2, h1, h2, h4⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 1000000 in
