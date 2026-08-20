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

def piCount (k : ℕ) : ℕ := #{p ∈ Finset.range (k + 1) | p.Prime}

theorem piCount_le_self (k : ℕ) : piCount k ≤ k := by
  have h : #{p ∈ Finset.range (k + 1) | p.Prime} ≤ #(Finset.Icc 2 k) := by
    apply Finset.card_le_card
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    exact Finset.mem_Icc.2 ⟨hp.2.two_le, by omega⟩
  have h2 : #(Finset.Icc 2 k) = k - 1 := by rw [Nat.card_Icc]; omega
  unfold piCount
  omega

set_option maxRecDepth 40000 in
set_option maxHeartbeats 1000000 in
/-- Every prime is `2`, `3`, or coprime to `6`, and among any six consecutive integers
at most two are coprime to `6`. -/
