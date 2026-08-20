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

lemma infinite_gap_le_of_prime_pairs (B : ℕ)
    (h : ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ p.Prime ∧ q.Prime ∧ p < q ∧ q ≤ p + B) :
    {n : ℕ | primeGap n ≤ B}.Infinite := by
  classical
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨p, q, hNp, hp, hq, hpq, hqle⟩ := h (Nat.nth Nat.Prime (N + 1))
  set j := Nat.count Nat.Prime p
  have hnthp : Nat.nth Nat.Prime j = p := Nat.nth_count hp
  have hNj : N + 1 < j := by
    apply (Nat.nth_lt_nth Nat.infinite_setOf_prime).1
    rw [hnthp]
    exact hNp
  refine ⟨j, ?_, by omega⟩
  have hle : Nat.nth Nat.Prime (j + 1) ≤ q :=
    nth_prime_succ_le_of_prime hq (by rw [hnthp]; exact hpq)
  simp only [Set.mem_setOf_eq, primeGap, hnthp]
  omega

/-- Having infinitely many gaps bounded by `B` is the same as frequently having a gap at
most `B`. -/
