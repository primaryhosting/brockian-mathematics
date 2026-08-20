import Mathlib

/-!
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Filter

/-- The `n`-th prime gap `p_{n+1} - p_n`, where `p_n = Nat.nth Nat.Prime n`. -/

theorem boundedPrimeGaps_iff :
    BoundedPrimeGaps ↔ ∃ B : ℕ, {n : ℕ | primeGap n ≤ B}.Infinite := by
  constructor
  · intro hlt
    obtain ⟨B, hB⟩ := ENat.ne_top_iff_exists.1 hlt.ne
    refine ⟨B, (infinite_gap_le_iff_frequently B).2 ?_⟩
    by_contra hcon
    rw [not_frequently] at hcon
    have hev : ∀ᶠ n in atTop, ((B : ℕ∞) + 1) ≤ (primeGap n : ℕ∞) := by
      filter_upwards [hcon] with n hn
      have : B + 1 ≤ primeGap n := by omega
      exact_mod_cast this
    have hge : ((B : ℕ∞) + 1) ≤ Filter.liminf (fun n => (primeGap n : ℕ∞)) atTop :=
      le_liminf_of_le (by isBoundedDefault) hev
    rw [← hB] at hge
    have : ((B + 1 : ℕ) : ℕ∞) ≤ ((B : ℕ) : ℕ∞) := by push_cast; exact hge
    have := (Nat.cast_le (α := ℕ∞)).1 this
    omega
  · rintro ⟨B, hB⟩
    have hfreq := (infinite_gap_le_iff_frequently B).1 hB
    have hle : Filter.liminf (fun n => (primeGap n : ℕ∞)) atTop ≤ (B : ℕ∞) :=
      liminf_le_of_frequently_le (hfreq.mono fun n hn => by exact_mod_cast hn)
    exact lt_of_le_of_lt hle (ENat.coe_lt_top B)

/-- For every `k` there is an admissible set of size `k`: the `k` primes
`p_k, p_{k+1}, …, p_{2k-1}`, all of which exceed `k`. -/
