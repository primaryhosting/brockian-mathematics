import Mathlib

/-!
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian

namespace BetrothedNumbers

/-- `m` and `n` form a *betrothed* (quasi-amicable) pair:
both are positive and `σ m = σ n = m + n + 1`. -/

lemma sigma_lt_four_mul {n : ℕ} (hn : 1 < n) (hcard : n.primeFactors.card ≤ 3) :
    σ 1 n < 4 * n := by
  have hlt := sigma_mul_prod_pred_lt hn
  have hle := prod_le_four_mul_prod_pred
    (S := n.primeFactors) (fun p hp => Nat.prime_of_mem_primeFactors hp) hcard
  have hpos : 0 < ∏ p ∈ n.primeFactors, (p - 1) := by
    refine Finset.prod_pos ?_
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have : σ 1 n * ∏ p ∈ n.primeFactors, (p - 1)
      < (4 * n) * ∏ p ∈ n.primeFactors, (p - 1) := by
    calc σ 1 n * ∏ p ∈ n.primeFactors, (p - 1)
        < n * ∏ p ∈ n.primeFactors, p := hlt
      _ ≤ n * (4 * ∏ p ∈ n.primeFactors, (p - 1)) := Nat.mul_le_mul_left _ hle
      _ = (4 * n) * ∏ p ∈ n.primeFactors, (p - 1) := by ring
  exact Nat.lt_of_mul_lt_mul_right this

/-- **Hagis–Lord, Proposition 2.** If `m` and `n` are coprime betrothed numbers, then
`m * n` has at least four distinct prime factors. -/
