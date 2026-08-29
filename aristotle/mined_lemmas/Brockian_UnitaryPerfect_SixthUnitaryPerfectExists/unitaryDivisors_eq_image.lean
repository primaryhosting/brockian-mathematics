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

/-!
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.UnitaryPerfect

open Finset

/-- `d` is a *unitary divisor* of `n` if `d ∣ n` and `d` is coprime to `n / d`. -/

lemma unitaryDivisors_eq_image {n : ℕ} (hn : n ≠ 0) :
    unitaryDivisors n =
      n.primeFactors.powerset.image (fun S => ∏ p ∈ S, p ^ n.factorization p) := by
  ext d
  simp only [mem_image, mem_powerset, mem_unitaryDivisors hn, IsUnitaryDivisor]
  constructor
  · rintro ⟨hdvd, hcop⟩
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact hn (Nat.eq_zero_of_zero_dvd hdvd)
    have hq0 : n / d ≠ 0 := by
      rintro h
      exact hn (by rw [← Nat.div_mul_cancel hdvd, h, zero_mul])
    have hfac : ∀ p ∈ d.primeFactors, d.factorization p = n.factorization p := by
      intro p hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
      have hnotdvd : ¬ p ∣ n / d := by
        intro hcontra
        have : p ∣ Nat.gcd d (n / d) := Nat.dvd_gcd hpd hcontra
        rw [hcop] at this
        exact hpp.one_lt.ne' (Nat.dvd_one.mp this)
      have hsplit : n = d * (n / d) := (Nat.mul_div_cancel' hdvd).symm
      have := congrArg (fun f => f p) (congrArg Nat.factorization hsplit)
      simp only [Nat.factorization_mul hd0 hq0, Finsupp.add_apply] at this
      rw [Nat.factorization_eq_zero_of_not_dvd hnotdvd] at this
      omega
    refine ⟨d.primeFactors, Nat.primeFactors_mono hdvd hn, ?_⟩
    calc ∏ p ∈ d.primeFactors, p ^ n.factorization p
        = ∏ p ∈ d.primeFactors, p ^ d.factorization p := by
          refine Finset.prod_congr rfl (fun p hp => ?_)
          rw [hfac p hp]
      _ = d := prod_primeFactors_pow_factorization hd0
  · rintro ⟨S, hS, rfl⟩
    set d := ∏ p ∈ S, p ^ n.factorization p with hd
    set e := ∏ p ∈ n.primeFactors \ S, p ^ n.factorization p with he
    have hde : d * e = n := by
      rw [hd, he, mul_comm, Finset.prod_sdiff hS, prod_primeFactors_pow_factorization hn]
    have hd0 : 0 < d := by
      refine Finset.prod_pos (fun p hp => ?_)
      exact pow_pos (Nat.prime_of_mem_primeFactors (hS hp)).pos _
    have hdvd : d ∣ n := ⟨e, hde.symm⟩
    have hdiv : n / d = e := by
      rw [← hde, Nat.mul_div_cancel_left _ hd0]
    refine ⟨hdvd, ?_⟩
    rw [hdiv]
    exact prod_pow_coprime_prod_pow hS (Finset.sdiff_subset) (Finset.disjoint_sdiff)

/-- Euler-product formula for the unitary divisor sum. -/
