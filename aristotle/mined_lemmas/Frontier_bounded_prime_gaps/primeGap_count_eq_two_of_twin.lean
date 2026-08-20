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
-/

open Filter

namespace Frontier

/-- `primeGap n = p_{n+1} - p_n`, where `p_n = Nat.nth Nat.Prime n` is the `n`-th prime
(so `p_0 = 2`, `p_1 = 3`, ...). -/

theorem primeGap_count_eq_two_of_twin {p : ℕ} (hp : p.Prime) (hp2 : (p + 2).Prime)
    (hne : p ≠ 2) : primeGap (Nat.count Nat.Prime p) = 2 := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hne)
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hnp1 : ¬ (p + 1).Prime := by
    intro h
    have hdvd : 2 ∣ (p + 1) := by omega
    rcases h.eq_one_or_self_of_dvd 2 hdvd with h' | h' <;> omega
  have hcount : Nat.count Nat.Prime (p + 2) = Nat.count Nat.Prime p + 1 := by
    rw [show p + 2 = (p + 1) + 1 from rfl, Nat.count_succ, Nat.count_succ]
    simp [hp, hnp1]
  have h1 : Nat.nth Nat.Prime (Nat.count Nat.Prime p) = p := Nat.nth_count hp
  have h2 : Nat.nth Nat.Prime (Nat.count Nat.Prime p + 1) = p + 2 := by
    rw [← hcount]; exact Nat.nth_count hp2
  unfold primeGap
  rw [h1, h2]
  omega

/-- **Conditional reduction:** the twin prime conjecture implies bounded prime gaps, with the
explicit bound `B = 2`. -/
