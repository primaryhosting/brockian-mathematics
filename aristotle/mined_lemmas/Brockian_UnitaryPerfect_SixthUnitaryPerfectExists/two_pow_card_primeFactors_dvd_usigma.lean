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

theorem two_pow_card_primeFactors_dvd_usigma {n : ℕ} (hn : n ≠ 0) (hodd : Odd n) :
    2 ^ n.primeFactors.card ∣ usigma n := by
  rw [usigma_eq_factorization_prod hn, Finsupp.prod, Nat.support_factorization]
  rw [← Finset.prod_const]
  refine Finset.prod_dvd_prod_of_dvd _ _ ?_
  intro p hp
  have hpodd : Odd p := by
    rcases Nat.Prime.eq_two_or_odd' (Nat.prime_of_mem_primeFactors hp) with rfl | h
    · exact absurd (Nat.dvd_of_mem_primeFactors hp) (by
        simpa [Nat.two_dvd_ne_zero, Nat.odd_iff] using hodd)
    · exact h
  have : Odd (p ^ n.factorization p) := hpodd.pow
  rcases this with ⟨t, ht⟩
  exact ⟨t + 1, by omega⟩

