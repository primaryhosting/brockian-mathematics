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

open Finset

namespace Brockian.GiugaNumbers

/-- A *Giuga number* is a composite number `n > 1` such that `p ∣ n / p - 1` for every
prime `p` dividing `n`. -/

lemma isOddGiugaSystem_primeFactors {n : ℕ} (hodd : Odd n) (h : IsGiuga n) :
    IsOddGiugaSystem n.primeFactors := by
  classical
  have hsf : Squarefree n := h.squarefree
  obtain ⟨hn1, hnp, hdvd⟩ := h
  have hprod : ∏ p ∈ n.primeFactors, p = n := Nat.prod_primeFactors_of_squarefree hsf
  have hprimes : ∀ p ∈ n.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have h0 : ∀ p ∈ n.primeFactors, p ≠ 0 := fun p hp => (hprimes p hp).ne_zero
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    refine ⟨hprimes p hp, (hprimes p hp).odd_of_ne_two ?_⟩
    rintro rfl
    have h2 : 2 ∣ n := Nat.dvd_of_mem_primeFactors hp
    have := Nat.odd_iff.mp hodd
    omega
  · by_contra hcard
    interval_cases hc : n.primeFactors.card
    · rw [Finset.card_eq_zero] at hc
      rw [hc] at hprod
      simp at hprod
      omega
    · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc
      rw [hp] at hprod hprimes
      simp only [Finset.prod_singleton] at hprod
      exact hnp (hprod ▸ hprimes p (Finset.mem_singleton_self p))
  · rw [criterion_iff hprimes]
    intro p hp
    have hdiv : n / p = ∏ q ∈ n.primeFactors.erase p, q := by
      conv_lhs => rw [← hprod]
      exact prod_div_eq_prod_erase h0 hp
    have hge : 1 ≤ n / p :=
      (Nat.one_le_div_iff (hprimes p hp).pos).mpr
        (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp))
    have := Int.natCast_dvd_natCast.mpr (hdvd p hp)
    rw [Nat.cast_sub hge] at this
    rw [hdiv] at this
    simpa [Nat.cast_prod] using this

/-- From an odd Giuga system one builds an odd Giuga number. -/
