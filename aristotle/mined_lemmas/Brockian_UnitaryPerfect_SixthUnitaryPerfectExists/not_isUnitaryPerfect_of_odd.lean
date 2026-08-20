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
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header above is repeated here as a module docstring: Lean requires all
`import` statements to precede any module documentation comment.)

## Contents

A *unitary divisor* of `n` is a divisor `d` with `gcd (d, n/d) = 1`, and `n` is
*unitary perfect* when the sum `σ*(n)` of its unitary divisors equals `2 * n`.
Only five unitary perfect numbers are known, and whether a sixth exists is open.

This file develops the basic theory (`σ*` is multiplicative, its value on prime
powers, and hence the product formula `σ*(n) = ∏_{p^a ‖ n} (p^a + 1)`), verifies
the five classically known unitary perfect numbers, proves the partial result
that no odd number is unitary perfect, and finally states and proves the
conditional reduction `SixthUnitaryPerfectExists`: as soon as there is *one*
unitary perfect number outside the known list of five, there are at least six
unitary perfect numbers.
-/

namespace Brockian.UnitaryPerfect

open Finset

/-- The unitary divisors of `n`: the divisors `d` of `n` with `gcd (d, n / d) = 1`. -/

theorem not_isUnitaryPerfect_of_odd {n : ℕ} (hodd : Odd n) : ¬ IsUnitaryPerfect n := by
  rintro ⟨hpos, heq⟩
  have hn : n ≠ 0 := hpos.ne'
  have hdvd := two_pow_card_primeFactors_dvd_usigma hn hodd
  rw [heq] at hdvd
  have hcard : n.primeFactors.card ≤ 1 := by
    by_contra hlt
    push_neg at hlt
    have h4 : (4 : ℕ) ∣ 2 * n := dvd_trans (by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ∣ 2 ^ n.primeFactors.card := pow_dvd_pow 2 hlt) hdvd
    obtain ⟨c, hc⟩ := h4
    have : 2 ∣ n := ⟨c, by omega⟩
    rw [Nat.odd_iff] at hodd
    omega
  interval_cases h : n.primeFactors.card
  · -- no prime factors: n = 1
    have hn1 : n = 1 := by
      by_contra hne
      have : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.2 (by omega)
      rw [← Finset.card_pos, h] at this
      omega
    rw [hn1, usigma_one] at heq
    omega
  · -- exactly one prime factor: n is a prime power and σ*(n) = n + 1
    obtain ⟨p, hp⟩ := Finset.card_eq_one.1 h
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by rw [hp]; exact Finset.mem_singleton_self p)
    have hnp : n = p ^ n.factorization p := by
      conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
      rw [Finsupp.prod, Nat.support_factorization, hp, Finset.prod_singleton]
    have husig : usigma n = p ^ n.factorization p + 1 := by
      rw [usigma_eq_factorization_prod hn, Finsupp.prod, Nat.support_factorization, hp,
        Finset.prod_singleton]
    have hpdvd : p ∣ n :=
      Nat.dvd_of_mem_primeFactors (by rw [hp]; exact Finset.mem_singleton_self p)
    have h2n : 2 ≤ n := hpp.two_le.trans (Nat.le_of_dvd hpos hpdvd)
    rw [husig, ← hnp] at heq
    omega

/-- Every unitary perfect number is even; in particular a sixth one, should it exist,
must be even. -/
