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
def IsGiuga (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ ∀ p ∈ n.primeFactors, p ∣ n / p - 1

/-- `30` is a Giuga number, so the notion is not vacuous. -/
lemma isGiuga_thirty : IsGiuga 30 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  have h : (30 : ℕ).primeFactors = {2, 3, 5} := by decide +kernel
  rw [h]
  decide

/-- Every Giuga number is squarefree. -/
lemma IsGiuga.squarefree {n : ℕ} (h : IsGiuga n) : Squarefree n := by
  obtain ⟨hn, hnp, hdvd⟩ := h
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have hpn : p ∈ n.primeFactors :=
    Nat.mem_primeFactors.2 ⟨hp, dvd_trans (dvd_mul_left p p) hpp, by omega⟩
  obtain ⟨k, hk⟩ := hpp
  have hdiv : n / p = p * k := by
    rw [hk, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
  have h1 : p ∣ n / p := ⟨k, hdiv⟩
  have h2 : p ∣ n / p - 1 := hdvd p hpn
  have h3 : p ∣ 1 := by
    have hsub := Nat.dvd_sub h1 h2
    have hge : 1 ≤ n / p := (Nat.one_le_div_iff hp.pos).2
      (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hpn))
    simpa [Nat.sub_sub_self hge] using hsub
  exact hp.one_lt.ne' (Nat.dvd_one.1 h3)

/-- If `p ≠ q` are prime divisors of `n`, then `q ∣ n / p`. -/
lemma dvd_div_of_ne {n p q : ℕ} (hp : p ∈ n.primeFactors) (hq : q ∈ n.primeFactors)
    (hne : q ≠ p) : q ∣ n / p := by
  obtain ⟨hpp, hpd, hn0⟩ := Nat.mem_primeFactors.1 hp
  obtain ⟨hqp, hqd, -⟩ := Nat.mem_primeFactors.1 hq
  obtain ⟨k, hk⟩ := hpd
  have hnp : n / p = k := by rw [hk, Nat.mul_div_cancel_left _ hpp.pos]
  rw [hnp]
  rcases (Nat.Prime.dvd_mul hqp).1 (hk ▸ hqd) with hd | hd
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hqp hpp).1 hd) hne
  · exact hd

/-- The key congruence: for a Giuga number `n`, we have `∑_{p ∣ n} n / p ≡ 1 (mod n)`. -/
lemma IsGiuga.dvd_sum_sub_one {n : ℕ} (h : IsGiuga n) :
    n ∣ (∑ p ∈ n.primeFactors, n / p) - 1 := by
  have hsq : Squarefree n := h.squarefree
  obtain ⟨hn, hnp, hdvd⟩ := h
  suffices h' : (∏ q ∈ n.primeFactors, q) ∣ (∑ p ∈ n.primeFactors, n / p) - 1 by
    rwa [Nat.prod_primeFactors_of_squarefree hsq] at h'
  refine Finset.prod_primes_dvd _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime) ?_
  intro p hp
  have hA : ∑ q ∈ n.primeFactors, n / q
      = ∑ q ∈ n.primeFactors.erase p, n / q + n / p := (Finset.sum_erase_add _ _ hp).symm
  have hR : p ∣ ∑ q ∈ n.primeFactors.erase p, n / q :=
    Finset.dvd_sum (fun q hq => dvd_div_of_ne (Finset.mem_of_mem_erase hq) hp
      (Finset.ne_of_mem_erase hq).symm)
  have hppos : 0 < p := (Nat.prime_of_mem_primeFactors hp).pos
  have h1 : 1 ≤ n / p := (Nat.one_le_div_iff hppos).2
    (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp))
  obtain ⟨s, hs⟩ := hdvd p hp
  obtain ⟨t, ht⟩ := hR
  have hnp' : n / p = p * s + 1 := by omega
  refine ⟨s + t, ?_⟩
  rw [hA, hnp', ht, Nat.mul_add]
  omega

/-- For a Giuga number, `∑_{p ∣ n} n / p ≥ n + 1`. -/
lemma IsGiuga.sum_ge {n : ℕ} (h : IsGiuga n) : n + 1 ≤ ∑ p ∈ n.primeFactors, n / p := by
  have hd := h.dvd_sum_sub_one
  obtain ⟨hn, hnp, hdvd⟩ := h
  obtain ⟨p, hp⟩ : (n.primeFactors).Nonempty := by
    rw [Nat.nonempty_primeFactors]; omega
  have hppos : 0 < p := (Nat.prime_of_mem_primeFactors hp).pos
  have hpd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have h1 : 1 ≤ n / p := (Nat.one_le_div_iff hppos).2 (Nat.le_of_dvd (by omega) hpd)
  have h2 : n / p ≠ 1 := by
    intro hone
    apply hnp
    have hnn : n = p := by
      have hmul := Nat.div_mul_cancel hpd
      rw [hone] at hmul; omega
    rw [hnn]; exact Nat.prime_of_mem_primeFactors hp
  have hle : n / p ≤ ∑ q ∈ n.primeFactors, n / q :=
    Finset.single_le_sum (f := fun q => n / q) (fun i _ => Nat.zero_le _) hp
  have hpos : 0 < (∑ q ∈ n.primeFactors, n / q) - 1 := by omega
  have := Nat.le_of_dvd hpos hd
  omega

/-- For a Giuga number, the sum of the reciprocals of its prime divisors exceeds `1`. -/
lemma IsGiuga.one_lt_sum_inv {n : ℕ} (h : IsGiuga n) :
    1 < ∑ p ∈ n.primeFactors, (1 : ℚ) / p := by
  have hge := h.sum_ge
  have hn : 1 < n := h.1
  have hcast : ((∑ p ∈ n.primeFactors, n / p : ℕ) : ℚ)
      = n * ∑ p ∈ n.primeFactors, (1 : ℚ) / p := by
    push_cast [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have hpd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hp0 : (p : ℚ) ≠ 0 := by
      have := (Nat.prime_of_mem_primeFactors hp).pos
      positivity
    rw [Nat.cast_div hpd hp0]
    field_simp
  have h1 : ((n : ℚ) + 1) ≤ n * ∑ p ∈ n.primeFactors, (1 : ℚ) / p := by
    rw [← hcast]; exact_mod_cast hge
  have hn0 : (0 : ℚ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  nlinarith [h1]

/-- For an antitone function, the sum over a finite set of indices is bounded by the sum over
the initial segment of the same size. -/
lemma sum_le_sum_range_of_antitone {f : ℕ → ℚ} (hf : Antitone f) (T : Finset ℕ) :
    ∑ i ∈ T, f i ≤ ∑ i ∈ range T.card, f i := by
  induction hk : T.card generalizing T with
  | zero => simp [Finset.card_eq_zero.1 hk]
  | succ k ih =>
    have hne : T.Nonempty := Finset.card_pos.1 (by omega)
    have hmem : T.max' hne ∈ T := T.max'_mem hne
    have hsub : T ⊆ range (T.max' hne + 1) := fun x hx =>
      Finset.mem_range.2 (Nat.lt_succ_of_le (T.le_max' x hx))
    have hcard : k + 1 ≤ T.max' hne + 1 := by
      calc k + 1 = T.card := hk.symm
        _ ≤ (range (T.max' hne + 1)).card := Finset.card_le_card hsub
        _ = T.max' hne + 1 := by simp
    have herase : (T.erase (T.max' hne)).card = k := by
      rw [Finset.card_erase_of_mem hmem, hk]
      omega
    have hih := ih (T.erase (T.max' hne)) herase
    have hsum : ∑ i ∈ T.erase (T.max' hne), f i + f (T.max' hne) = ∑ i ∈ T, f i :=
      Finset.sum_erase_add T f hmem
    have hle : f (T.max' hne) ≤ f k := hf (by omega)
    rw [← hsum, Finset.sum_range_succ]
    linarith

/-- Enumeration of the numbers `≥ 5` that are coprime to `6`: `5, 7, 11, 13, 17, 19, 23, 25, …`. -/
def coprimeSixEnum (i : ℕ) : ℕ := 6 * (i / 2) + 5 + 2 * (i % 2)

/-- The index of a number `≥ 5` coprime to `6` in the enumeration `coprimeSixEnum`. -/
def coprimeSixIndex (p : ℕ) : ℕ := if p % 6 = 5 then 2 * (p / 6) else 2 * (p / 6) - 1

lemma coprimeSixEnum_index {p : ℕ} (h5 : 5 ≤ p) (h : p % 6 = 1 ∨ p % 6 = 5) :
    coprimeSixEnum (coprimeSixIndex p) = p := by
  unfold coprimeSixEnum coprimeSixIndex
  split <;> omega

lemma coprimeSixEnum_mono : Monotone coprimeSixEnum := by
  intro a b hab
  unfold coprimeSixEnum
  omega

lemma coprimeSixEnum_pos (i : ℕ) : 0 < coprimeSixEnum i := by
  unfold coprimeSixEnum; omega

lemma antitone_inv_coprimeSixEnum : Antitone (fun i => (1 : ℚ) / coprimeSixEnum i) := by
  intro a b hab
  have hmono := coprimeSixEnum_mono hab
  have ha : (0 : ℚ) < coprimeSixEnum a := by exact_mod_cast coprimeSixEnum_pos a
  have hb : (coprimeSixEnum a : ℚ) ≤ coprimeSixEnum b := by exact_mod_cast hmono
  exact one_div_le_one_div_of_le ha hb

/-- The sum of reciprocals over a finite set of numbers `≥ 5` coprime to `6` is bounded by the
sum of the reciprocals of the first `|S|` such numbers. -/
lemma sum_inv_le_of_coprime_six {S : Finset ℕ}
    (hS : ∀ p ∈ S, 5 ≤ p ∧ (p % 6 = 1 ∨ p % 6 = 5)) :
    ∑ p ∈ S, (1 : ℚ) / p ≤ ∑ i ∈ range S.card, (1 : ℚ) / coprimeSixEnum i := by
  have hinv : ∀ p ∈ S, coprimeSixEnum (coprimeSixIndex p) = p :=
    fun p hp => coprimeSixEnum_index (hS p hp).1 (hS p hp).2
  have hinj : ∀ a ∈ S, ∀ b ∈ S, coprimeSixIndex a = coprimeSixIndex b → a = b := by
    intro a ha b hb hab
    rw [← hinv a ha, ← hinv b hb, hab]
  have hcard : (S.image coprimeSixIndex).card = S.card := Finset.card_image_of_injOn hinj
  have hsum : ∑ i ∈ S.image coprimeSixIndex, (1 : ℚ) / coprimeSixEnum i
      = ∑ p ∈ S, (1 : ℚ) / p := by
    rw [Finset.sum_image hinj]
    exact Finset.sum_congr rfl (fun p hp => by rw [hinv p hp])
  rw [← hsum, ← hcard]
  exact sum_le_sum_range_of_antitone antitone_inv_coprimeSixEnum _

/-- Prime divisors of an odd Giuga number other than `3` are `≥ 5` and coprime to `6`. -/
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
theorem odd_giuga_nine_le_card_primeFactors {n : ℕ} (hodd : Odd n) (h : IsGiuga n) :
    9 ≤ n.primeFactors.card := by
  by_contra hlt
  push_neg at hlt
  have hsum := h.one_lt_sum_inv
  by_cases h3 : 3 ∈ n.primeFactors
  · have hS' : ∀ p ∈ n.primeFactors.erase 3, 5 ≤ p ∧ (p % 6 = 1 ∨ p % 6 = 5) :=
      fun p hp => primeFactor_props hodd (Finset.mem_of_mem_erase hp) (Finset.ne_of_mem_erase hp)
    have hcard' : (n.primeFactors.erase 3).card ≤ 7 := by
      rw [Finset.card_erase_of_mem h3]; omega
    have hb := sum_inv_le_of_coprime_six hS'
    have hmono : ∑ i ∈ range (n.primeFactors.erase 3).card, (1 : ℚ) / coprimeSixEnum i
        ≤ ∑ i ∈ range 7, (1 : ℚ) / coprimeSixEnum i := by
      have hsubr : range (n.primeFactors.erase 3).card ⊆ range 7 :=
        Finset.range_subset_range.mpr hcard'
      refine Finset.sum_le_sum_of_subset_of_nonneg hsubr ?_
      intro i _ _
      positivity
    have hsplit : ∑ p ∈ n.primeFactors, (1 : ℚ) / p
        = (1 : ℚ) / 3 + ∑ p ∈ n.primeFactors.erase 3, (1 : ℚ) / p := by
      rw [← Finset.add_sum_erase _ _ h3]
      norm_num
    have hnum : (1 : ℚ) / 3 + ∑ i ∈ range 7, (1 : ℚ) / coprimeSixEnum i < 1 := by
      simp [Finset.sum_range_succ, coprimeSixEnum]
      norm_num
    rw [hsplit] at hsum
    linarith
  · have hS' : ∀ p ∈ n.primeFactors, 5 ≤ p ∧ (p % 6 = 1 ∨ p % 6 = 5) := by
      intro p hp
      exact primeFactor_props hodd hp (by rintro rfl; exact h3 hp)
    have hcard' : n.primeFactors.card ≤ 8 := by omega
    have hb := sum_inv_le_of_coprime_six hS'
    have hmono : ∑ i ∈ range n.primeFactors.card, (1 : ℚ) / coprimeSixEnum i
        ≤ ∑ i ∈ range 8, (1 : ℚ) / coprimeSixEnum i := by
      have hsubr : range n.primeFactors.card ⊆ range 8 := Finset.range_subset_range.mpr hcard'
      refine Finset.sum_le_sum_of_subset_of_nonneg hsubr ?_
      intro i _ _
      positivity
    have hnum : ∑ i ∈ range 8, (1 : ℚ) / coprimeSixEnum i < 1 := by
      simp [Finset.sum_range_succ, coprimeSixEnum]
      norm_num
    linarith

/-- **Conditional reduction for the existence of an odd Giuga number.**

Whether an odd Giuga number exists is an open problem, so what is proved here is the conditional
statement: if an odd Giuga number exists, then one exists which is moreover squarefree and has at
least nine distinct prime factors. -/
theorem OddGiugaExists :
    (∃ n : ℕ, Odd n ∧ IsGiuga n) →
      ∃ n : ℕ, Odd n ∧ IsGiuga n ∧ Squarefree n ∧ 9 ≤ n.primeFactors.card := by
  rintro ⟨n, hodd, h⟩
  exact ⟨n, hodd, h, h.squarefree, odd_giuga_nine_le_card_primeFactors hodd h⟩

end Brockian.GiugaNumbers

