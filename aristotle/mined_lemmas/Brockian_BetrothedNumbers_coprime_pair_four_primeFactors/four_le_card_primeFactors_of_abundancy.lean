/-
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Brockian.BetrothedNumbers

open ArithmeticFunction

/-- `m` and `n` form a *betrothed* (quasi-amicable) pair: they are distinct positive
integers with `σ m = σ n = m + n + 1`. -/

lemma four_le_card_primeFactors_of_abundancy {N : ℕ} (hN : 0 < N) (h : 4 * N < sigma 1 N) :
    4 ≤ N.primeFactors.card := by
  by_contra hcon
  push_neg at hcon
  have hcard : N.primeFactors.card ≤ 3 := by omega
  set Q := ∏ p ∈ N.primeFactors, (p - 1) with hQ
  set P := ∏ p ∈ N.primeFactors, p with hP
  have hQpos : 0 < Q := by
    rw [hQ]
    refine Finset.prod_pos fun p hp => ?_
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have h1 : 4 * N * Q < sigma 1 N * Q := (Nat.mul_lt_mul_right hQpos).mpr h
  have h2 := sigma_mul_prod_pred_le hN.ne'
  have h3 := prod_le_four_mul_prod_pred (fun p hp => Nat.prime_of_mem_primeFactors hp) hcard
  have h4 : N * P ≤ N * (4 * Q) := Nat.mul_le_mul_left _ h3
  nlinarith

/-- **Hagis–Lord, Proposition 2.**  If `m` and `n` are coprime betrothed numbers, then
`m * n` has at least four distinct prime factors.

The proof: coprimality and multiplicativity of `σ` give `σ(mn) = (m+n+1)^2 > 4mn`, so
`mn` has abundancy `> 4`; but a number with at most three distinct prime factors has
abundancy `< ∏ p/(p-1) ≤ 2 · (3/2) · (5/4) = 15/4 < 4`. -/
