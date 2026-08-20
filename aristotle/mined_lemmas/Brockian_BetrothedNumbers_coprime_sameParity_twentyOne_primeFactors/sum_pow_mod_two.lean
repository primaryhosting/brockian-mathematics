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
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian.BetrothedNumbers

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

/-- `Betrothed m n` says that `(m, n)` is a betrothed (quasi-amicable) pair:
both are positive and `σ m = σ n = m + n + 1`. -/

lemma sum_pow_mod_two {p : ℕ} (hp : Odd p) (m : ℕ) : (∑ k ∈ range m, p ^ k) % 2 = m % 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      have : p ^ m % 2 = 1 := Nat.odd_iff.mp hp.pow
      omega

/-- For a positive odd `n`, the divisor sum `σ n` is odd if and only if `n` is a perfect square. -/
