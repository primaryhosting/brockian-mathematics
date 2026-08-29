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

/-- `primeGap n = p_{n+1} - p_n`, the gap between the `n`-th and `(n+1)`-st prime
(with `p_0 = 2`, i.e. `p_n = Nat.nth Nat.Prime n`). -/

theorem dhl2_of_twinPrimeConjecture (h : TwinPrimeConjecture) : DHL2 := by
  refine ⟨{0, 2}, fun N => ?_⟩
  obtain ⟨p, hNp, hp, hp2⟩ := h N
  refine ⟨p, hNp, ?_⟩
  have hfil : ({0, 2} : Finset ℕ).filter (fun k => Nat.Prime (p + k)) = {0, 2} := by
    refine Finset.filter_true_of_mem fun k hk => ?_
    fin_cases hk
    · simpa using hp
    · simpa using hp2
  rw [hfil]
  decide

/-- Consequence: the twin prime conjecture implies that the `liminf` of prime gaps is
finite. -/
