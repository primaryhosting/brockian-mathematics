import Mathlib

/-!
# Is Betrothed Pair Iff Nontrivial Two Cycle
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.Dynamics.isBetrothedPair_iff_nontrivial_twoCycle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat

set_option autoImplicit false

namespace Brockian.BetrothedNumbers

/-- The sum-of-divisors function `σ₁(n) = ∑_{d ∣ n} d`, i.e. `ArithmeticFunction.sigma 1`. -/

lemma le_sigmaOne {n : ℕ} (hn : 0 < n) : n ≤ sigmaOne n := by
  rw [sigmaOne_eq_sum]
  exact Finset.single_le_sum (f := fun d => d) (fun _ _ => Nat.zero_le _)
    (Nat.mem_divisors_self n hn.ne')

/-- If `partner m = n` with `m` and `n` positive, then no truncation occurred in the
natural subtraction, i.e. `σ₁(m) = m + n + 1`. -/
