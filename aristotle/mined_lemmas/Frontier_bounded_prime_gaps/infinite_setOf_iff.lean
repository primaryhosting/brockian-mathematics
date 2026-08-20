import Mathlib

/-!
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

open Filter

/-- `primeGap n = p_{n+1} - p_n`, where `p_n = Nat.nth Nat.Prime n` is the `n`-th prime
(with `p_0 = 2`). -/

lemma infinite_setOf_iff (p : ℕ → Prop) :
    {n : ℕ | p n}.Infinite ↔ ∀ N : ℕ, ∃ n ≥ N, p n := by
  constructor
  · intro h N
    obtain ⟨n, hn, hlt⟩ := h.exists_gt N
    exact ⟨n, hlt.le, hn⟩
  · intro h
    apply Set.infinite_of_forall_exists_gt
    intro a
    obtain ⟨n, hn, hp⟩ := h (a + 1)
    exact ⟨n, hp, by omega⟩

/-- In `ℕ∞`, an infimum over a tail is bounded by a natural number iff some term is. -/
