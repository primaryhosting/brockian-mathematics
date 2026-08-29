/-
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header above is repeated as a plain comment at the very top of the file, since Lean 4
does not allow a module docstring to precede the `import` commands.)
-/

open Filter

namespace Frontier

/-- The `n`-th prime number (`nthPrime 0 = 2`). -/

lemma frequently_gap_le_iff (B : ℕ) :
    (∃ᶠ n in atTop, primeGap n ≤ B) ↔
      ∀ N : ℕ, ∃ p q : ℕ, N ≤ p ∧ p.Prime ∧ q.Prime ∧ p < q ∧ q ≤ p + B := by
  constructor
  · intro h N
    have htend : Tendsto nthPrime atTop atTop := nthPrime_strictMono.tendsto_atTop
    have hev : ∀ᶠ n in atTop, N ≤ nthPrime n := htend.eventually_ge_atTop N
    obtain ⟨n, hgap, hge⟩ := (h.and_eventually hev).exists
    exact ⟨nthPrime n, nthPrime (n + 1), hge, nthPrime_prime n, nthPrime_prime (n + 1),
      nthPrime_lt_nthPrime_succ n, nthPrime_succ_le_of_gap_le hgap⟩
  · intro h
    rw [frequently_atTop]
    intro M
    obtain ⟨p, q, hNp, hp, hq, hpq, hqp⟩ := h (nthPrime M + 1)
    refine ⟨Nat.count Nat.Prime p, ?_, ?_⟩
    · have : nthPrime M < nthPrime (Nat.count Nat.Prime p) := by
        rw [nthPrime_count hp]; omega
      exact le_of_lt (nthPrime_strictMono.lt_iff_lt.1 this)
    · have h1 : nthPrime (Nat.count Nat.Prime p + 1) ≤ q := nthPrime_succ_count_le hp hq hpq
      have h2 : nthPrime (Nat.count Nat.Prime p) = p := nthPrime_count hp
      unfold primeGap
      omega

/-- `liminf` over `ℕ∞` is finite iff the sequence is frequently bounded by some natural number. -/
