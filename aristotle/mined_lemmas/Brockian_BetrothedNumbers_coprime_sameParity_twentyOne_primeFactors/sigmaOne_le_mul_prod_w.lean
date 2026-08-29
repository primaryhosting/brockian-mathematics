/-
# Coprime Same Parity Twenty One Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_sameParity_twentyOne_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

namespace Brockian
namespace BetrothedNumbers

open Finset

/-! ## Basic definitions -/

/-- `sigmaOne n` is the sum-of-divisors function `σ₁(n) = ∑_{d ∣ n} d`. -/

lemma sigmaOne_le_mul_prod_w :
    ∀ (N : ℕ), N ≠ 0 → (sigmaOne N : ℚ) ≤ (N : ℚ) * ∏ p ∈ N.primeFactors, w p := by
  intro N
  induction N using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
      intro _
      rw [Nat.primeFactors_prime_pow hk.ne' hp, Finset.prod_singleton]
      push_cast
      exact sigmaOne_prime_pow_le hp
  | zero => intro h; exact absurd rfl h
  | one => intro _; simp [sigmaOne]
  | coprime a b ha hb hab iha ihb =>
      intro _
      have ha0 : a ≠ 0 := by omega
      have hb0 : b ≠ 0 := by omega
      have hsig : (sigmaOne (a * b) : ℚ) = (sigmaOne a : ℚ) * (sigmaOne b : ℚ) := by
        unfold sigmaOne
        rw [hab.sum_divisors_mul]
        push_cast
        ring
      have hpf : (a * b).primeFactors = a.primeFactors ∪ b.primeFactors := hab.primeFactors_mul
      have hdisj : Disjoint a.primeFactors b.primeFactors := hab.disjoint_primeFactors
      rw [hsig, hpf, Finset.prod_union hdisj]
      have h1 := iha ha0
      have h2 := ihb hb0
      have hA : 0 ≤ ∏ p ∈ a.primeFactors, w p :=
        Finset.prod_nonneg fun p hp => w_nonneg (Nat.prime_of_mem_primeFactors hp).two_le
      have hB : 0 ≤ ∏ p ∈ b.primeFactors, w p :=
        Finset.prod_nonneg fun p hp => w_nonneg (Nat.prime_of_mem_primeFactors hp).two_le
      calc (sigmaOne a : ℚ) * (sigmaOne b : ℚ)
          ≤ ((a:ℚ) * ∏ p ∈ a.primeFactors, w p) * ((b:ℚ) * ∏ p ∈ b.primeFactors, w p) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = ((a * b : ℕ) : ℚ) * ((∏ p ∈ a.primeFactors, w p) * ∏ p ∈ b.primeFactors, w p) := by
            push_cast; ring

/-! ## The greedy bound on `∏ p/(p-1)` over a set of odd primes -/

/-- The twenty smallest odd primes. -/
