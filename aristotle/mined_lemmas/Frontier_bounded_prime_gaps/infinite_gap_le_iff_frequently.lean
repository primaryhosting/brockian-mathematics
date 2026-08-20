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

lemma infinite_gap_le_iff_frequently (B : ℕ) :
    {n : ℕ | primeGap n ≤ B}.Infinite ↔ ∃ᶠ n in atTop, primeGap n ≤ B := by
  constructor
  · intro hinf
    rw [frequently_atTop]
    intro a
    obtain ⟨n, hn, hna⟩ := hinf.exists_gt a
    exact ⟨n, hna.le, hn⟩
  · intro hfreq
    apply Set.infinite_of_forall_exists_gt
    intro a
    obtain ⟨b, hb, hbp⟩ := frequently_atTop.1 hfreq (a + 1)
    exact ⟨b, hbp, by omega⟩

/-- Reformulation of finiteness of the `liminf` of the prime gaps. -/
