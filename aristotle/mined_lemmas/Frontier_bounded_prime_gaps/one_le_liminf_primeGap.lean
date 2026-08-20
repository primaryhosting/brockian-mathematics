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

/-- `nthPrime n` is the `n`-th prime number, counting from `nthPrime 0 = 2`. -/

theorem one_le_liminf_primeGap : 1 ≤ liminf (fun n => (primeGap n : ℕ∞)) atTop := by
  rw [Filter.liminf_eq_iSup_iInf_of_nat]
  refine le_trans ?_ (le_iSup (fun n : ℕ => ⨅ i, ⨅ _ : n ≤ i, (primeGap i : ℕ∞)) 0)
  exact le_iInf₂ fun i _ => by exact_mod_cast one_le_primeGap i

/-- If `q` is a prime strictly larger than the `k`-th prime, then the `(k+1)`-st prime
is at most `q`: the `(k+1)`-st prime is the least prime exceeding the `k`-th one. -/
