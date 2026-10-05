import Mathlib
/-!
# Coprime Same Parity Twenty One Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_sameParity_twentyOne_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian.BetrothedNumbers

open ArithmeticFunction

/-- A *betrothed* (quasi-amicable) pair: two positive integers, each of whose
divisor sums equals the sum of the pair plus one. -/

lemma oddPrimeBound_mono {j k : ℕ} (hjk : j ≤ k) : oddPrimeBound j ≤ oddPrimeBound k := by
  induction k, hjk using Nat.le_induction with
  | base => exact le_refl _
  | succ k _ ih =>
      refine ih.trans ?_
      rw [oddPrimeBound_succ]
      nlinarith [one_le_oddPrimeBound k, one_le_abFactor (Nat.prime_nth_prime (k + 1)).two_le]

/-- A nonempty finite set of `k` odd primes, all at most `m`, forces `m` to be at
least the `k`-th odd prime `Nat.nth Nat.Prime k`. -/
