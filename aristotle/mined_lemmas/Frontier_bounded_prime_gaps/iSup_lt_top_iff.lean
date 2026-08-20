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

lemma iSup_lt_top_iff (g : ℕ → ℕ∞) :
    (⨆ N, g N) < ⊤ ↔ ∃ B : ℕ, ∀ N, g N ≤ (B : ℕ∞) := by
  constructor
  · intro h
    obtain ⟨B, hB⟩ := ENat.ne_top_iff_exists.mp h.ne
    exact ⟨B, fun N => hB ▸ le_iSup g N⟩
  · rintro ⟨B, hB⟩
    exact lt_of_le_of_lt (iSup_le hB) (by simp)

/-! ### Main reduction -/

/-- **Bounded prime gaps (statement / Lean-checked reduction).**

The `liminf` of the sequence of prime gaps `p_{n+1} - p_n`, computed in `ℕ∞`, is finite
if and only if some bound `B` is attained by infinitely many prime gaps.

This is a Lean-checked reduction of the Zhang–Maynard theorem to the combinatorial
statement `BoundedPrimeGaps`; the equivalence itself is proved unconditionally. -/
