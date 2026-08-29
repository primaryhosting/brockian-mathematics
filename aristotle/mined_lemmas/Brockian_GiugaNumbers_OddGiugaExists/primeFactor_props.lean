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
# Odd Giuga Exists
Category: Brockian Conjecture
Target: Brockian.GiugaNumbers.OddGiugaExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.GiugaNumbers

open Finset

/-- A *Giuga number* is a composite number `n > 1` such that every prime `p` dividing `n`
satisfies `p ∣ n / p - 1`. -/

lemma primeFactor_props {n p : ℕ} (hodd : Odd n) (hp : p ∈ n.primeFactors) (hp3 : p ≠ 3) :
    5 ≤ p ∧ (p % 6 = 1 ∨ p % 6 = 5) := by
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have hp2 : p ≠ 2 := by
    rintro rfl
    rw [Nat.odd_iff] at hodd
    omega
  have hpodd : p % 2 = 1 := Nat.odd_iff.1 (hpp.odd_of_ne_two hp2)
  have hp3' : p % 3 ≠ 0 := by
    intro h3
    have : (3 : ℕ) ∣ p := Nat.dvd_of_mod_eq_zero h3
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hpp).1 this).symm
  have hge2 : 2 ≤ p := hpp.two_le
  omega

/-- **Any odd Giuga number has at least nine distinct prime factors.** -/
