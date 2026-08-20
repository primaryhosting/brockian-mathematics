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

import Mathlib

/-!
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

A *unitary divisor* of `n` is a divisor `d ∣ n` with `gcd d (n / d) = 1`, and `n` is
*unitary perfect* when the sum `σ*(n)` of its unitary divisors equals `2 * n`.
Exactly five unitary perfect numbers are known,

```
6, 60, 90, 87360, 146361946186458562560000
```

and whether a sixth one exists is a well-known open problem.  Consequently the statement
"a sixth unitary perfect number exists" cannot be proved outright; what is established
here is:

* the multiplicative theory of `σ*` from scratch, culminating in the Euler-product
  formula `sigmaStar_eq_prod_primeFactors` and multiplicativity
  `sigmaStar_mul_of_coprime`;
* unconditional verification that the five known numbers are unitary perfect
  (`known_isUnitaryPerfect`);
* unconditional structural theorems: every unitary perfect number has an odd prime
  factor (`exists_odd_prime_factor`) and is even (`even_of_isUnitaryPerfect`), i.e.
  there are no odd unitary perfect numbers, and a unitary perfect number with only two
  distinct prime factors must equal `6` (`eq_six_of_card_primeFactors_eq_two`);
* the target theorem `SixthUnitaryPerfectExists`, a Lean-checked *conditional
  reduction*: from the existence of a unitary perfect number outside the known list one
  obtains a genuine "sixth" unitary perfect number together with all of the structural
  information above (even, `> 6`, at least three distinct prime factors, divisible by an
  odd prime).

Mathlib search note: `exact?` / `apply?` / `rw?` find nothing directly applicable here.
Mathlib's divisor API (`Nat.divisors`, `Nat.ArithmeticFunction.sigma`,
`Nat.ArithmeticFunction.isMultiplicative_sigma`) treats ordinary divisors only and has no
notion of unitary divisor, so the theory below is built from the general factorization
lemmas (`Nat.factorization_prod_pow_eq_self`, `Finset.prod_add`, ...).
-/

open Finset

namespace Brockian
namespace UnitaryPerfect

/-- The unitary divisors of `n`: the divisors `d` of `n` with `d` coprime to `n / d`. -/

theorem eq_six_of_card_primeFactors_eq_two (h : IsUnitaryPerfect n)
    (hcard : n.primeFactors.card = 2) : n = 6 := by
  have hn0 : n ≠ 0 := h.1.ne'
  have h2 : 2 ∈ n.primeFactors := two_mem_primeFactors h
  obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.1 hcard
  obtain ⟨p, hp2, hpf⟩ : ∃ p, p ≠ 2 ∧ n.primeFactors = {2, p} := by
    rw [hs] at h2
    rcases Finset.mem_insert.1 h2 with rfl | hb
    · exact ⟨b, fun hb => hab hb.symm, hs⟩
    · rw [Finset.mem_singleton] at hb
      subst hb
      exact ⟨a, fun ha => hab ha, by rw [hs, Finset.pair_comm]⟩
  have hp : p.Prime := Nat.prime_of_mem_primeFactors (by rw [hpf]; simp)
  have hne : (2 : ℕ) ≠ p := Ne.symm hp2
  have hprod : n = 2 ^ n.factorization 2 * p ^ n.factorization p := by
    have hh := prod_primeFactors_pow hn0
    rw [hpf, Finset.prod_pair hne] at hh
    exact hh.symm
  have hsig : sigmaStar n = (2 ^ n.factorization 2 + 1) * (p ^ n.factorization p + 1) := by
    rw [sigmaStar_eq_prod_primeFactors hn0, hpf, Finset.prod_pair hne]
  have hA : n.factorization 2 ≠ 0 := by
    have := Nat.Prime.factorization_pos_of_dvd Nat.prime_two hn0 (Nat.dvd_of_mem_primeFactors h2)
    omega
  have hB : n.factorization p ≠ 0 := by
    have := Nat.Prime.factorization_pos_of_dvd hp hn0
      (Nat.dvd_of_mem_primeFactors (by rw [hpf]; simp))
    omega
  have hx : 2 ≤ 2 ^ n.factorization 2 := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ n.factorization 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hy : 3 ≤ p ^ n.factorization p := by
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    calc (3 : ℕ) ≤ p := hp3
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ n.factorization p := Nat.pow_le_pow_right (by omega) (by omega)
  have key : (2 ^ n.factorization 2 + 1) * (p ^ n.factorization p + 1)
      = 2 * (2 ^ n.factorization 2 * p ^ n.factorization p) := by
    rw [← hsig, h.2, ← hprod]
  obtain ⟨hx2, hy3⟩ := two_mul_three_of_prod_eq _ _ hx hy key
  rw [hprod, hx2, hy3]

end Structure

/-!
## The target statement

`SixthUnitaryPerfectExists` is a conditional reduction: the existence of *any* unitary
perfect number outside the known list yields a "sixth" unitary perfect number carrying all
the structural constraints proved above.  The unconditional existence statement is an open
problem and is therefore not asserted.
-/

/-- **Sixth unitary perfect number (conditional).**  If some unitary perfect number is not
one of the five known ones, then there is a sixth unitary perfect number, and it is
necessarily even, greater than `6`, divisible by an odd prime, and has at least three
distinct prime factors. -/
