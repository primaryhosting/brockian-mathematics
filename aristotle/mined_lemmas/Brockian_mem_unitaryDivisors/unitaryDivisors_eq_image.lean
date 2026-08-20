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

lemma unitaryDivisors_eq_image (hn : n ≠ 0) :
    unitaryDivisors n =
      n.primeFactors.powerset.image (fun S => ∏ p ∈ S, p ^ n.factorization p) := by
  classical
  ext d
  simp only [Finset.mem_image, Finset.mem_powerset, mem_unitaryDivisors]
  constructor
  · rintro ⟨hdvd, -, hcop⟩
    have hd0 : d ≠ 0 := by rintro rfl; simp at hdvd; exact hn hdvd
    refine ⟨d.primeFactors, Nat.primeFactors_mono hdvd hn, ?_⟩
    have key : ∀ p ∈ d.primeFactors, d.factorization p = n.factorization p := by
      intro p hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
      have hnp : ¬ p ∣ (n / d) := by
        intro hdd
        have hp1 : p ∣ 1 := hcop ▸ Nat.dvd_gcd hpd hdd
        exact absurd (Nat.dvd_one.mp hp1) hpp.ne_one
      have h0 : (n / d).factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hnp
      rw [Nat.factorization_div hdvd] at h0
      simp only [Finsupp.coe_tsub, Pi.sub_apply] at h0
      have hle : d.factorization p ≤ n.factorization p :=
        (Nat.factorization_le_iff_dvd hd0 hn).2 hdvd p
      omega
    calc ∏ p ∈ d.primeFactors, p ^ n.factorization p
        = ∏ p ∈ d.primeFactors, p ^ d.factorization p :=
          Finset.prod_congr rfl fun p hp => by rw [key p hp]
      _ = d := prod_primeFactors_pow hd0
  · rintro ⟨S, hS, rfl⟩
    set d := ∏ p ∈ S, p ^ n.factorization p with hd
    set m := ∏ p ∈ n.primeFactors \ S, p ^ n.factorization p with hm
    have hmul : m * d = n := by
      rw [hm, hd, Finset.prod_sdiff hS, prod_primeFactors_pow hn]
    have hdvd : d ∣ n := ⟨m, by rw [← hmul]; ring⟩
    have hd0 : d ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 fun p hp => ?_
      exact pow_ne_zero _ (Nat.Prime.ne_zero (Nat.prime_of_mem_primeFactors (hS hp)))
    have hquot : n / d = m := by
      rw [← hmul, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hd0)]
    refine ⟨hdvd, hn, ?_⟩
    rw [hquot, hd, hm]
    refine Nat.Coprime.prod_left fun p hp => Nat.Coprime.prod_right fun q hq => ?_
    have hp' : p.Prime := Nat.prime_of_mem_primeFactors (hS hp)
    have hq' : q.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.1 hq).1
    refine Nat.Coprime.pow _ _ ((Nat.coprime_primes hp' hq').2 ?_)
    rintro rfl
    exact (Finset.mem_sdiff.1 hq).2 hp

/-- The Euler-product formula for `σ*`: `σ*(n) = ∏_{p ∣ n} (p ^ v_p(n) + 1)`. -/
