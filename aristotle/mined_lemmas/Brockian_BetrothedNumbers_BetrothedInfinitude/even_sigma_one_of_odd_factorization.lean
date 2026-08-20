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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian.BetrothedNumbers

/-- Two positive integers `m ≠ n` form a *betrothed* (or *quasi-amicable*) pair when the sum of
the divisors of each, excluding `1` and the number itself, equals the other number; equivalently
`σ m = σ n = m + n + 1`. -/

theorem even_sigma_one_of_odd_factorization {m p : ℕ} (hm : m ≠ 0) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpm : p ∣ m) (hodd : Odd (m.factorization p)) : Even (σ 1 m) := by
  have hfac : σ 1 m = m.factorization.prod fun q k => σ 1 (q ^ k) :=
    isMultiplicative_sigma.multiplicative_factorization _ hm
  have hmem : p ∈ m.factorization.support := by
    rw [Nat.support_factorization]
    exact Nat.mem_primeFactors.2 ⟨hp, hpm, hm⟩
  have hdvd : σ 1 (p ^ m.factorization p) ∣ σ 1 m := by
    rw [hfac]; exact Finset.dvd_prod_of_mem _ hmem
  have heven : Even (σ 1 (p ^ m.factorization p)) := by
    rw [sigma_one_apply_prime_pow hp]
    have hone : ∀ j ∈ Finset.range (m.factorization p + 1), p ^ j % 2 = 1 := fun j _ =>
      Nat.odd_iff.1 (hp.odd_of_ne_two hp2).pow
    rw [Nat.even_iff, Finset.sum_nat_mod, Finset.sum_congr rfl hone]
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
    obtain ⟨t, ht⟩ := hodd
    omega
  exact even_iff_two_dvd.2 ((even_iff_two_dvd.1 heven).trans hdvd)

/-- In a betrothed pair whose two members have the same parity, every odd prime occurs to an even
power (so each member is a square or twice a square). -/
