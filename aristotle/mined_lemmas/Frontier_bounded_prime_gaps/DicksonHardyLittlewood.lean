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

def DicksonHardyLittlewood (k : ℕ) : Prop :=
  ∀ H : Finset ℕ, H.card = k → IsAdmissible H →
    {n : ℕ | 2 ≤ (H.filter fun h => Nat.Prime (n + h)).card}.Infinite

section Basic

