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
-/

set_option maxHeartbeats 1000000

namespace Brockian.CarmichaelKorselt

/-- A Carmichael number: a composite `n > 1` which is a Fermat pseudoprime to every base
coprime to it. -/

theorem isCarmichael_of_three_primes {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (h1 : (p - 1) ∣ (p * q * r - 1)) (h2 : (q - 1) ∣ (p * q * r - 1))
    (h3 : (r - 1) ∣ (p * q * r - 1)) : IsCarmichael (p * q * r) := by
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hr2 := hr.two_le
  have hcpq : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hcpr : Nat.Coprime p r := (Nat.coprime_primes hp hr).mpr hpr
  have hcqr : Nat.Coprime q r := (Nat.coprime_primes hq hr).mpr hqr
  have hpq2 : 2 * 2 ≤ p * q := Nat.mul_le_mul hp2 hq2
  have hlt : 1 < p * q * r := by
    have := Nat.mul_le_mul hpq2 hr2
    omega
  refine ⟨hlt, ?_, ?_⟩
  · exact Nat.not_prime_mul (by omega) (by omega)
  · intro a ha
    have hap : Nat.Coprime a p := Nat.Coprime.coprime_dvd_right ⟨q * r, by ring⟩ ha
    have haq : Nat.Coprime a q := Nat.Coprime.coprime_dvd_right ⟨p * r, by ring⟩ ha
    have har : Nat.Coprime a r := Nat.Coprime.coprime_dvd_right ⟨p * q, by ring⟩ ha
    have e1 : a ^ (p * q * r - 1) ≡ 1 [MOD p] := pow_modEq_one_of_sub_one_dvd hp h1 hap
    have e2 : a ^ (p * q * r - 1) ≡ 1 [MOD q] := pow_modEq_one_of_sub_one_dvd hq h2 haq
    have e3 : a ^ (p * q * r - 1) ≡ 1 [MOD r] := pow_modEq_one_of_sub_one_dvd hr h3 har
    have e12 : a ^ (p * q * r - 1) ≡ 1 [MOD p * q] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hcpq).mp ⟨e1, e2⟩
    exact (Nat.modEq_and_modEq_iff_modEq_mul (Nat.Coprime.mul_left hcpr hcqr)).mp ⟨e12, e3⟩

/-- The Chernick construction: if `6k+1`, `12k+1`, `18k+1` are all prime (`k > 0`), then their
product is a Carmichael number with three distinct prime factors. -/
