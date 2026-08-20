/-!
# Odd Giuga Exists
Category: Brockian Conjecture
Target: Brockian.GiugaNumbers.OddGiugaExists
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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
def IsGiuga (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ ∀ p ∈ n.primeFactors, p ∣ n / p - 1

/-- An *odd Giuga system* is a finite set `S` of at least two odd primes satisfying Giuga's
rational criterion `∑_{p ∈ S} 1/p - ∏_{p ∈ S} 1/p ∈ ℤ`. -/
def IsOddGiugaSystem (S : Finset ℕ) : Prop :=
  (∀ p ∈ S, p.Prime ∧ Odd p) ∧ 2 ≤ S.card ∧
    ∃ k : ℤ, (∑ p ∈ S, (p : ℚ)⁻¹) - (∏ p ∈ S, (p : ℚ)⁻¹) = (k : ℚ)

section Helpers

variable {S : Finset ℕ}

/-- In a product of nonzero naturals, dividing by one factor leaves the product of the others. -/
lemma prod_div_eq_prod_erase (h0 : ∀ q ∈ S, q ≠ 0) {p : ℕ} (hp : p ∈ S) :
    (∏ q ∈ S, q) / p = ∏ q ∈ S.erase p, q := by
  rw [← Finset.mul_prod_erase S (fun q => q) hp]
  exact Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (h0 p hp))

/-- Divisibility of Giuga's numerator by a single prime of the system. -/
lemma dvd_numerator_iff {p : ℕ} (hp : p ∈ S) :
    (p : ℤ) ∣ ((∑ q ∈ S, ∏ r ∈ S.erase q, (r : ℤ)) - 1) ↔
      (p : ℤ) ∣ ((∏ r ∈ S.erase p, (r : ℤ)) - 1) := by
  classical
  have key : (∑ q ∈ S, ∏ r ∈ S.erase q, (r : ℤ)) - 1
      = ((∏ r ∈ S.erase p, (r : ℤ)) - 1) + ∑ q ∈ S.erase p, ∏ r ∈ S.erase q, (r : ℤ) := by
    rw [← Finset.add_sum_erase S _ hp]; ring
  have hdvd : (p : ℤ) ∣ ∑ q ∈ S.erase p, ∏ r ∈ S.erase q, (r : ℤ) := by
    refine Finset.dvd_sum fun q hq => ?_
    have hne : q ≠ p := (Finset.mem_erase.mp hq).1
    exact Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨Ne.symm hne, hp⟩)
  rw [key]
  refine ⟨fun h => ?_, fun h => h.add hdvd⟩
  simpa using dvd_sub h hdvd

/-- Divisibility of Giuga's numerator by the whole product. -/
lemma prod_dvd_numerator_iff (hS : ∀ p ∈ S, p.Prime) :
    ((∏ p ∈ S, p : ℕ) : ℤ) ∣ ((∑ q ∈ S, ∏ r ∈ S.erase q, (r : ℤ)) - 1) ↔
      ∀ p ∈ S, (p : ℤ) ∣ ((∏ r ∈ S.erase p, (r : ℤ)) - 1) := by
  classical
  constructor
  · intro h p hp
    refine (dvd_numerator_iff hp).mp (dvd_trans ?_ h)
    exact_mod_cast Int.natCast_dvd_natCast.mpr (Finset.dvd_prod_of_mem _ hp)
  · intro h
    rw [Nat.cast_prod]
    refine Finset.prod_dvd_of_coprime ?_ fun p hp => (dvd_numerator_iff hp).mpr (h p hp)
    intro p hp q hq hne
    simp only [Function.onFun]
    exact Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes (hS p hp) (hS q hq)).mpr hne)

/-- Giuga's expression written as a single fraction. -/
lemma sum_inv_sub_prod_inv (h0 : ∀ q ∈ S, q ≠ 0) :
    (∑ p ∈ S, (p : ℚ)⁻¹) - (∏ p ∈ S, (p : ℚ)⁻¹)
      = (((∑ q ∈ S, ∏ r ∈ S.erase q, (r : ℤ)) - 1 : ℤ) : ℚ) / ((∏ p ∈ S, p : ℕ) : ℚ) := by
  classical
  have hne : ∀ q ∈ S, (q : ℚ) ≠ 0 := fun q hq => Nat.cast_ne_zero.mpr (h0 q hq)
  have hN : ((∏ p ∈ S, p : ℕ) : ℚ) ≠ 0 := by
    rw [Nat.cast_prod]
    exact Finset.prod_ne_zero_iff.mpr hne
  rw [eq_div_iff hN, sub_mul, Finset.sum_mul]
  have h1 : ∀ p ∈ S, (p : ℚ)⁻¹ * ((∏ q ∈ S, q : ℕ) : ℚ) = ∏ r ∈ S.erase p, (r : ℚ) := by
    intro p hp
    rw [Nat.cast_prod, ← Finset.mul_prod_erase S (fun q => ((q : ℚ))) hp, ← mul_assoc,
      inv_mul_cancel₀ (hne p hp), one_mul]
  have h2 : (∏ p ∈ S, (p : ℚ)⁻¹) * ((∏ q ∈ S, q : ℕ) : ℚ) = 1 := by
    rw [Nat.cast_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun p hp => inv_mul_cancel₀ (hne p hp)
  rw [Finset.sum_congr rfl h1, h2]
  push_cast
  ring

/-- The rational criterion is equivalent to the divisibility criterion. -/
lemma criterion_iff (hS : ∀ p ∈ S, p.Prime) :
    (∃ k : ℤ, (∑ p ∈ S, (p : ℚ)⁻¹) - (∏ p ∈ S, (p : ℚ)⁻¹) = (k : ℚ)) ↔
      ∀ p ∈ S, (p : ℤ) ∣ ((∏ r ∈ S.erase p, (r : ℤ)) - 1) := by
  have h0 : ∀ q ∈ S, q ≠ 0 := fun q hq => (hS q hq).ne_zero
  have hN' : (∏ x ∈ S, (x : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun q hq => Nat.cast_ne_zero.mpr (h0 q hq)
  have hN : ((∏ p ∈ S, p : ℕ) : ℚ) ≠ 0 := by rw [Nat.cast_prod]; exact hN'
  rw [← prod_dvd_numerator_iff hS, sum_inv_sub_prod_inv h0]
  constructor
  · rintro ⟨k, hk⟩
    rw [div_eq_iff hN] at hk
    refine ⟨k, ?_⟩
    have : ((((∑ q ∈ S, ∏ r ∈ S.erase q, (r : ℤ)) - 1 : ℤ)) : ℚ)
        = (((∏ p ∈ S, p : ℕ) : ℤ) * k : ℤ) := by push_cast; push_cast at hk; linarith
    exact_mod_cast this
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [hk]
    push_cast
    exact mul_div_cancel_left₀ _ hN'

end Helpers

/-- Every Giuga number is squarefree. -/
lemma IsGiuga.squarefree {n : ℕ} (h : IsGiuga n) : Squarefree n := by
  obtain ⟨hn1, -, hdvd⟩ := h
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have hn0 : n ≠ 0 := by omega
  have hpn : p ∣ n := dvd_trans (Dvd.intro p rfl) hpp
  have hmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpn, hn0⟩
  have h1 : p ∣ n / p := by
    obtain ⟨m, hm⟩ := hpp
    exact ⟨m, by rw [hm, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]⟩
  have h2 := hdvd p hmem
  have hge : 1 ≤ n / p := (Nat.one_le_div_iff hp.pos).mpr (Nat.le_of_dvd (by omega) hpn)
  have hone : p ∣ 1 := by simpa [Nat.sub_sub_self hge] using Nat.dvd_sub h1 h2
  exact hp.one_lt.ne' (Nat.dvd_one.mp hone)

/-- From an odd Giuga number one extracts an odd Giuga system. -/
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

lemma primeFactors_thirty : (30 : ℕ).primeFactors = {2, 3, 5} := by
  have h : ∏ p ∈ ({2, 3, 5} : Finset ℕ), p = 30 := by decide
  rw [← h]
  exact Nat.primeFactors_prod (by decide)

/-- `30` is a Giuga number, so the notion `IsGiuga` is not vacuous. -/
lemma isGiuga_thirty : IsGiuga 30 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [primeFactors_thirty]
  decide

/-- Giuga's rational criterion for the (even) Giuga number `30`. -/
lemma criterion_thirty :
    (∑ p ∈ ({2, 3, 5} : Finset ℕ), (p : ℚ)⁻¹) - (∏ p ∈ ({2, 3, 5} : Finset ℕ), (p : ℚ)⁻¹) = 1 := by
  norm_num

/-- **Odd Giuga numbers exist iff an odd Giuga system exists.**

Whether an odd Giuga number exists is an open problem; this theorem is a Lean-checked
reduction of that existence statement to Giuga's rational criterion: there is an odd Giuga
number if and only if there is a finite set `S` of at least two odd primes with
`∑_{p ∈ S} 1/p - ∏_{p ∈ S} 1/p ∈ ℤ`. -/
theorem OddGiugaExists :
    (∃ n : ℕ, Odd n ∧ IsGiuga n) ↔ (∃ S : Finset ℕ, IsOddGiugaSystem S) := by
  constructor
  · rintro ⟨n, hodd, hn⟩
    exact ⟨n.primeFactors, isOddGiugaSystem_primeFactors hodd hn⟩
  · rintro ⟨S, hS⟩
    exact ⟨∏ p ∈ S, p, (isGiuga_prod hS).1, (isGiuga_prod hS).2⟩

/-- Conditional form of the target: any odd Giuga system produces an odd Giuga number. -/
theorem oddGiuga_exists_of_system {S : Finset ℕ} (hS : IsOddGiugaSystem S) :
    ∃ n : ℕ, Odd n ∧ IsGiuga n :=
  OddGiugaExists.mpr ⟨S, hS⟩

end Brockian.GiugaNumbers

