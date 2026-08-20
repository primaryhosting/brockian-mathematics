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

def IsAdmissible (H : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

/-- The Dickson–Hardy–Littlewood type hypothesis `DHL[k, 2]`: for every admissible set `H`
of size `k` there are infinitely many `n` such that at least two of the numbers `n + h`,
`h ∈ H`, are prime.  This is what the Goldston–Pintz–Yıldırım / Zhang / Maynard sieve
machinery provides for suitable `k`. -/
