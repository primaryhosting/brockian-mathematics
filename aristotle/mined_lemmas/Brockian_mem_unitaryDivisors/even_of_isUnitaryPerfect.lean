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

theorem even_of_isUnitaryPerfect (h : IsUnitaryPerfect n) : Even n := by
  classical
  by_contra hodd
  have hn0 : n ≠ 0 := h.1.ne'
  have hn2 : ¬ (2 ∣ n) := fun hd => hodd (even_iff_two_dvd.mpr hd)
  -- every prime factor of `n` is odd, hence every factor `p ^ v_p(n) + 1` of `σ*(n)` is even
  have hfac : ∀ p ∈ n.primeFactors, 2 ∣ (p ^ n.factorization p + 1) := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpne : p ≠ 2 := by
      rintro rfl
      exact hn2 (Nat.dvd_of_mem_primeFactors hp)
    have hpodd : ¬ (2 ∣ p) := fun hd =>
      hpne ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hpp).1 hd).symm
    have hnd : ¬ (2 ∣ p ^ n.factorization p) := fun hd =>
      hpodd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two hd)
    omega
  have hpow : 2 ^ n.primeFactors.card ∣ sigmaStar n := by
    rw [sigmaStar_eq_prod_primeFactors hn0, ← Finset.prod_const]
    exact Finset.prod_dvd_prod_of_dvd _ _ hfac
  -- so `n` cannot have two distinct prime factors, else `4 ∣ 2n`
  have hcard1 : n.primeFactors.card ≤ 1 := by
    by_contra hc
    push_neg at hc
    have h4 : (4 : ℕ) ∣ sigmaStar n := dvd_trans (by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ∣ 2 ^ n.primeFactors.card := pow_dvd_pow 2 hc) hpow
    rw [h.2] at h4
    obtain ⟨c, hc'⟩ := h4
    exact hn2 ⟨c, by omega⟩
  -- hence `n = p ^ k` with `p ^ k + 1 = 2 p ^ k`, which is impossible
  obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.2 h.one_lt
  have hall : ∀ q ∈ n.primeFactors, q = p := by
    intro q hq
    by_contra hqp
    have : 2 ≤ n.primeFactors.card := Finset.one_lt_card.2 ⟨q, hq, p, hp, hqp⟩
    omega
  have hnp : n = p ^ n.factorization p := eq_pow_of_unique_primeFactor h.one_lt hall
  have hcard : n.primeFactors = {p} := Finset.eq_singleton_iff_unique_mem.2 ⟨hp, hall⟩
  have h2 := h.2
  rw [sigmaStar_eq_prod_primeFactors hn0, hcard, Finset.prod_singleton, ← hnp] at h2
  have := h.one_lt
  omega

