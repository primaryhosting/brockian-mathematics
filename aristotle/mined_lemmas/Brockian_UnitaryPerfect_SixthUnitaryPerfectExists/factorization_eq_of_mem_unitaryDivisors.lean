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

namespace Brockian.UnitaryPerfect

open Finset

/-- The unitary divisors of `n`: divisors `d` with `gcd (d, n / d) = 1`. -/

lemma factorization_eq_of_mem_unitaryDivisors {n d p : ℕ}
    (hd : d ∈ unitaryDivisors n) (hp : p ∈ d.primeFactors) :
    d.factorization p = n.factorization p := by
  rw [mem_unitaryDivisors] at hd
  obtain ⟨⟨hdvd, hn⟩, hcop⟩ := hd
  obtain ⟨hpp, hpd, hd0⟩ := Nat.mem_primeFactors.mp hp
  have hq0 : n / d ≠ 0 := by
    intro h
    rw [Nat.div_eq_zero_iff] at h
    rcases h with h | h
    · exact hd0 h
    · exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd) (by omega)
  have hnd : n = d * (n / d) := (Nat.mul_div_cancel' hdvd).symm
  have hpq : ¬ p ∣ (n / d) := by
    intro h
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hpd hcop) h
    exact hpp.one_lt.ne' this
  rw [hnd, Nat.factorization_mul hd0 hq0]
  simp [Nat.factorization_eq_zero_of_not_dvd hpq]

/-- The prime factors of a product of prime powers with nonzero exponents. -/
