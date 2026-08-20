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

lemma isGiuga_prod {S : Finset ℕ} (h : IsOddGiugaSystem S) :
    Odd (∏ p ∈ S, p) ∧ IsGiuga (∏ p ∈ S, p) := by
  classical
  obtain ⟨hodd, hcard, hcrit⟩ := h
  set n : ℕ := ∏ p ∈ S, p with hn
  have hprimes : ∀ p ∈ S, p.Prime := fun p hp => (hodd p hp).1
  have h0 : ∀ p ∈ S, p ≠ 0 := fun p hp => (hprimes p hp).ne_zero
  have hn0 : n ≠ 0 := Finset.prod_ne_zero_iff.mpr h0
  have hpf : n.primeFactors = S := Nat.primeFactors_prod hprimes
  obtain ⟨p, q, hpS, hqS, hpq⟩ := Finset.one_lt_card_iff.mp hcard
  have hpdvd : p ∣ n := Finset.dvd_prod_of_mem _ hpS
  have hn1 : 1 < n := lt_of_lt_of_le (hprimes p hpS).one_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpdvd)
  have hmp : n = p * ∏ r ∈ S.erase p, r := (Finset.mul_prod_erase S (fun q => q) hpS).symm
  have hmne : (∏ r ∈ S.erase p, r) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun r hr => h0 r (Finset.mem_of_mem_erase hr)
  have hqm : q ∣ ∏ r ∈ S.erase p, r :=
    Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨Ne.symm hpq, hqS⟩)
  have hm1 : (∏ r ∈ S.erase p, r) ≠ 1 := by
    intro hcon
    have := Nat.le_of_dvd (by omega) hqm
    rw [hcon] at this
    exact absurd this (by simpa using (hprimes q hqS).one_lt)
  have hnotprime : ¬ n.Prime := by
    rw [hmp]
    exact Nat.not_prime_mul (hprimes p hpS).one_lt.ne' hm1
  refine ⟨?_, hn1, hnotprime, ?_⟩
  · rw [Nat.odd_iff]
    by_contra hpar
    have h2 : 2 ∣ n := by omega
    have h2S : (2 : ℕ) ∈ S := hpf ▸ Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2, hn0⟩
    have := Nat.odd_iff.mp (hodd 2 h2S).2
    omega
  · intro r hr
    rw [hpf] at hr
    have hdiv : n / r = ∏ s ∈ S.erase r, s := prod_div_eq_prod_erase h0 hr
    have hint := (criterion_iff hprimes).mp hcrit r hr
    have hge : 1 ≤ ∏ s ∈ S.erase r, s :=
      Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun s hs =>
        h0 s (Finset.mem_of_mem_erase hs))
    rw [hdiv]
    have : ((r : ℕ) : ℤ) ∣ ((∏ s ∈ S.erase r, s : ℕ) - 1 : ℕ) := by
      rw [Nat.cast_sub hge]
      simpa [Nat.cast_prod] using hint
    exact_mod_cast this

/-! ### Sanity checks: the smallest Giuga number is `30 = 2 * 3 * 5` (which is even) -/

