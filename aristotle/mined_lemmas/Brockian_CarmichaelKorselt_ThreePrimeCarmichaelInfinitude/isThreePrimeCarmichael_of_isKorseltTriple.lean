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
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The unconditional infinitude of Carmichael numbers with exactly three prime factors is an
open problem.  This file gives a fully checked *conditional reduction*: Korselt's criterion
is proved in the three-prime case, reducing the conjecture to the purely arithmetic statement
`InfinitelyManyKorseltTriples`, and further to a Dickson-type prime-triple hypothesis via
Chernick's parametrisation `(6k+1)(12k+1)(18k+1)`.
-/

namespace Brockian.CarmichaelKorselt

/-- A *Carmichael number*: a composite `n > 1` such that `a ^ (n - 1) ≡ 1 [MOD n]` for every
`a` coprime to `n`. -/

theorem isThreePrimeCarmichael_of_isKorseltTriple {p q r : ℕ} (h : IsKorseltTriple p q r) :
    IsThreePrimeCarmichael (p * q * r) := by
  obtain ⟨hp, hq, hr, hpq, hqr, hdp, hdq, hdr⟩ := h
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hr2 := hr.two_le
  have hpne : p ≠ q := Nat.ne_of_lt hpq
  have hqne : q ≠ r := Nat.ne_of_lt hqr
  have hpne' : p ≠ r := Nat.ne_of_lt (lt_trans hpq hqr)
  have hcpq : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpne
  have hcpr : Nat.Coprime p r := (Nat.coprime_primes hp hr).mpr hpne'
  have hcqr : Nat.Coprime q r := (Nat.coprime_primes hq hr).mpr hqne
  have h4 : 4 * p ≤ p * q * r := by
    calc 4 * p = p * 2 * 2 := by ring
      _ ≤ p * q * r := Nat.mul_le_mul (Nat.mul_le_mul le_rfl hq2) hr2
  have hlt : 1 < p * q * r := by omega
  refine ⟨⟨hlt, ?_, ?_⟩, p, q, r, hp, hq, hr, hpq, hqr, rfl⟩
  · -- compositeness
    intro hprime
    rcases (Nat.Prime.eq_one_or_self_of_dvd hprime p ⟨q * r, by ring⟩) with h1 | h1
    · omega
    · omega
  · intro a hcop
    have hap : Nat.Coprime a p := Nat.Coprime.coprime_dvd_right ⟨q * r, by ring⟩ hcop
    have haq : Nat.Coprime a q := Nat.Coprime.coprime_dvd_right ⟨p * r, by ring⟩ hcop
    have har : Nat.Coprime a r := Nat.Coprime.coprime_dvd_right ⟨p * q, by ring⟩ hcop
    have e1 : a ^ (p * q * r - 1) ≡ 1 [MOD p] := pow_modEq_one_of_sub_one_dvd hp hdp hap
    have e2 : a ^ (p * q * r - 1) ≡ 1 [MOD q] := pow_modEq_one_of_sub_one_dvd hq hdq haq
    have e3 : a ^ (p * q * r - 1) ≡ 1 [MOD r] := pow_modEq_one_of_sub_one_dvd hr hdr har
    have e12 : a ^ (p * q * r - 1) ≡ 1 [MOD p * q] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hcpq).mp ⟨e1, e2⟩
    have hcpqr : Nat.Coprime (p * q) r := Nat.Coprime.mul_left hcpr hcqr
    exact (Nat.modEq_and_modEq_iff_modEq_mul hcpqr).mp ⟨e12, e3⟩

/-- **Conditional reduction.** If there are arbitrarily large Korselt triples of primes, then
there are infinitely many Carmichael numbers with exactly three prime factors. -/
