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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian.BetrothedNumbers

open ArithmeticFunction

/-- `m` and `n` form a *betrothed* (quasi-amicable) pair: both are positive, distinct, and
the sum of the divisors of each equals `m + n + 1`. -/

lemma four_mul_sigma_le_of_card_le_three {N : ℕ} (hN : N ≠ 0)
    (hcard : N.primeFactors.card ≤ 3) :
    4 * sigma 1 N ≤ 15 * N := by
  set P := ∏ p ∈ N.primeFactors, p with hP
  set P' := ∏ p ∈ N.primeFactors, (p - 1) with hP'
  have hP'pos : 0 < P' := by
    rw [hP']
    refine Finset.prod_pos ?_
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have h1 : sigma 1 N * P' ≤ N * P := sigma_mul_prod_pred_le hN
  have h2 : 4 * P ≤ 15 * P' :=
    four_mul_prod_le_of_card_le_three (fun p hp => Nat.prime_of_mem_primeFactors hp) hcard
  have h3 : (4 * sigma 1 N) * P' ≤ (15 * N) * P' := by
    calc (4 * sigma 1 N) * P' = 4 * (sigma 1 N * P') := by ring
      _ ≤ 4 * (N * P) := Nat.mul_le_mul_left 4 h1
      _ = N * (4 * P) := by ring
      _ ≤ N * (15 * P') := Nat.mul_le_mul_left N h2
      _ = (15 * N) * P' := by ring
  exact Nat.le_of_mul_le_mul_right h3 hP'pos

/-- **Hagis–Lord, Proposition 2.** If `m` and `n` are coprime betrothed numbers, then `m * n`
has at least four distinct prime factors.

Indeed `σ(mn) = σ(m)σ(n) = (m + n + 1)^2 > 4mn` by multiplicativity of `σ` and AM–GM, while a
number with at most three distinct prime factors satisfies `σ(N) ≤ (15/4) N < 4N`. -/
