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

lemma prod_pow_mem_unitaryDivisors {n : ℕ} (hn : n ≠ 0) {t : Finset ℕ}
    (ht : t ⊆ n.primeFactors) :
    (∏ p ∈ t, p ^ n.factorization p) ∈ unitaryDivisors n := by
  classical
  set d := ∏ p ∈ t, p ^ n.factorization p with hd
  set c := ∏ p ∈ n.primeFactors \ t, p ^ n.factorization p with hc
  have hprod : c * d = n := by
    rw [hc, hd, Finset.prod_sdiff ht, prod_primeFactors_pow_factorization hn]
  have hcop : Nat.Coprime d c := by
    refine Nat.Coprime.prod_left fun p hpt => Nat.Coprime.prod_right fun q hq => ?_
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (ht hpt)
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hq).1
    refine Nat.Coprime.pow _ _ ?_
    rw [Nat.coprime_primes hpp hqp]
    rintro rfl
    exact (Finset.mem_sdiff.mp hq).2 hpt
  have hdvd : d ∣ n := ⟨c, by rw [← hprod]; ring⟩
  have hd0 : d ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p hp =>
      pow_ne_zero _ (Nat.prime_of_mem_primeFactors (ht hp)).ne_zero
  have hdiv : n / d = c := by
    rw [← hprod, Nat.mul_div_assoc _ (dvd_refl d), Nat.div_self (Nat.pos_of_ne_zero hd0), mul_one]
  rw [mem_unitaryDivisors, hdiv]
  exact ⟨⟨hdvd, hn⟩, hcop⟩

