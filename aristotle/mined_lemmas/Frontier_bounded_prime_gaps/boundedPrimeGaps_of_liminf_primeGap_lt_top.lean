/-
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Filter

namespace Frontier

/-- The `n`-th prime number (`primeSeq 0 = 2`). -/

theorem boundedPrimeGaps_of_liminf_primeGap_lt_top
    (H : liminf (fun n => (primeGap n : ℕ∞)) atTop < ⊤) : BoundedPrimeGaps := by
  set L := liminf (fun n => (primeGap n : ℕ∞)) atTop with hL
  obtain ⟨B, hB⟩ : ∃ B : ℕ, L = (B : ℕ∞) := ⟨L.toNat, by
    lift L to ℕ using H.ne_top with m
    simp⟩
  refine ⟨B, ?_⟩
  by_contra hfin
  rw [Set.not_infinite] at hfin
  have hev : ∀ᶠ n in atTop, ((B + 1 : ℕ) : ℕ∞) ≤ (primeGap n : ℕ∞) := by
    have hnf : ¬ ∃ᶠ n in atTop, primeGap n ≤ B := by
      rw [Nat.frequently_atTop_iff_infinite]
      exact Set.not_infinite.2 hfin
    rw [Filter.not_frequently] at hnf
    filter_upwards [hnf] with n hn
    have : B + 1 ≤ primeGap n := by omega
    exact_mod_cast this
  have h2 := Filter.le_liminf_of_le (by isBoundedDefault) hev
  rw [← hL, hB] at h2
  have : (B + 1 : ℕ) ≤ (B : ℕ) := by exact_mod_cast h2
  omega

/-- The two formulations of bounded prime gaps are equivalent. -/
