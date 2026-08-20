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

namespace Brockian.UnitaryPerfect

open Finset

/-- The unitary divisors of `n`: the divisors `d` of `n` with `gcd d (n / d) = 1`. -/

theorem usigma_split {n : ℕ} (hn : 1 < n) :
    ∃ q m : ℕ, 1 < q ∧ q * m = n ∧ Nat.Coprime q m ∧ usigma n = (q + 1) * usigma m := by
  have hn0 : n ≠ 0 := by omega
  set p := n.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpd : p ∣ n := Nat.minFac_dvd n
  set k := n.factorization p
  have hk : k ≠ 0 := by
    have := (Nat.Prime.factorization_pos_of_dvd hp hn0 hpd)
    omega
  refine ⟨p ^ k, n / p ^ k, Nat.one_lt_pow hk hp.one_lt, Nat.ordProj_mul_ordCompl_eq_self n p, ?_, ?_⟩
  · exact Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp hn0)
  · have hcop : Nat.Coprime (p ^ k) (n / p ^ k) :=
      Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp hn0)
    have hm0 : n / p ^ k ≠ 0 := by
      intro h
      have := Nat.ordProj_mul_ordCompl_eq_self n p
      rw [h] at this
      omega
    calc usigma n = usigma (p ^ k * (n / p ^ k)) := by rw [Nat.ordProj_mul_ordCompl_eq_self n p]
      _ = usigma (p ^ k) * usigma (n / p ^ k) :=
          usigma_mul_of_coprime (pow_ne_zero _ hp.pos.ne') hm0 hcop
      _ = (p ^ k + 1) * usigma (n / p ^ k) := by rw [usigma_prime_pow hp hk]

