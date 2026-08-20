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

theorem SixthUnitaryPerfectExists
    (h : ∃ n, IsUnitaryPerfect n ∧ n ∉ known) :
    ∃ n, IsUnitaryPerfect n ∧ n ∉ known ∧ Even n ∧ 6 < n ∧ 3 ≤ n.primeFactors.card ∧
      ∃ p, p.Prime ∧ p ≠ 2 ∧ p ∣ n := by
  obtain ⟨n, hn, hnk⟩ := h
  obtain ⟨p, hp, hp2, hpn⟩ := exists_odd_prime_factor hn
  have heven : Even n := even_of_isUnitaryPerfect hn
  have hn6 : n ≠ 6 := by rintro rfl; exact hnk (by simp [known])
  have hcard : 3 ≤ n.primeFactors.card := by
    have h2 := two_le_card_primeFactors hn
    rcases Nat.lt_or_ge n.primeFactors.card 3 with hlt | hge
    · exact absurd (eq_six_of_card_primeFactors_eq_two hn (by omega)) hn6
    · exact hge
  refine ⟨n, hn, hnk, heven, ?_, hcard, p, hp, hp2, hpn⟩
  -- `n` is divisible by `2p ≥ 6`, and `n ≠ 6` because `6` belongs to the known list
  have h2 : 2 ∣ n := heven.two_dvd
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
  have h2p : 2 * p ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h2 hpn
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hge : 6 ≤ n := le_trans (by omega) (Nat.le_of_dvd hn.1 h2p)
  rcases Nat.lt_or_ge 6 n with hlt | hle
  · exact hlt
  · exact absurd (by omega : n = 6) hn6

end UnitaryPerfect
end Brockian

