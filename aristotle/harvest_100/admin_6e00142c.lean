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
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Brockian.PracticalNumbers

/-- A positive natural number `n` is *practical* when every `m ≤ n` can be written as a sum
of distinct divisors of `n`. -/
def Practical (n : ℕ) : Prop :=
  0 < n ∧ ∀ m ≤ n, ∃ S ⊆ n.divisors, ∑ d ∈ S, d = m

/-- A "complete sequence" lemma: if every element of a finite set of naturals is at most one
more than the sum of the strictly smaller elements, then every `m` up to the total sum is a
subset sum. -/
lemma exists_subset_sum_of_chain :
    ∀ D : Finset ℕ, (∀ x ∈ D, x ≤ 1 + ∑ y ∈ D.filter (fun y => y < x), y) →
      ∀ m ≤ ∑ x ∈ D, x, ∃ S ⊆ D, ∑ d ∈ S, d = m := by
  intro D
  induction D using Finset.strongInduction with
  | _ D IH =>
    intro hchain m hm
    rcases D.eq_empty_or_nonempty with rfl | hne
    · simp only [Finset.sum_empty, Nat.le_zero] at hm
      exact ⟨∅, by simp [hm]⟩
    · set x0 := D.max' hne with hx0def
      have hx0D : x0 ∈ D := D.max'_mem hne
      set D' := D.erase x0 with hD'def
      have hsub : D' ⊂ D := Finset.erase_ssubset hx0D
      have hfilter : D.filter (fun y => y < x0) = D' := by
        ext y
        simp only [Finset.mem_filter, hD'def, Finset.mem_erase]
        constructor
        · rintro ⟨hy, hlt⟩; exact ⟨ne_of_lt hlt, hy⟩
        · rintro ⟨hne', hy⟩
          exact ⟨hy, lt_of_le_of_ne (D.le_max' y hy) hne'⟩
      have hsum : ∑ x ∈ D, x = x0 + ∑ x ∈ D', x := (Finset.add_sum_erase _ _ hx0D).symm
      have hchain' : ∀ x ∈ D', x ≤ 1 + ∑ y ∈ D'.filter (fun y => y < x), y := by
        intro x hx
        have hxD : x ∈ D := Finset.mem_of_mem_erase hx
        have heq : D'.filter (fun y => y < x) = D.filter (fun y => y < x) := by
          ext y
          simp only [Finset.mem_filter, hD'def, Finset.mem_erase]
          constructor
          · rintro ⟨⟨_, hy⟩, hlt⟩; exact ⟨hy, hlt⟩
          · rintro ⟨hy, hlt⟩
            refine ⟨⟨?_, hy⟩, hlt⟩
            rintro rfl
            exact absurd (D.le_max' x hxD) (not_le.mpr hlt)
        rw [heq]
        exact hchain x hxD
      by_cases hcase : m ≤ ∑ x ∈ D', x
      · obtain ⟨S, hS, hSsum⟩ := IH D' hsub hchain' m hcase
        exact ⟨S, hS.trans (Finset.erase_subset _ _), hSsum⟩
      · push_neg at hcase
        have hx0le : x0 ≤ m := by
          have := hchain x0 hx0D
          rw [hfilter] at this
          omega
        have hle : m - x0 ≤ ∑ x ∈ D', x := by omega
        obtain ⟨S, hS, hSsum⟩ := IH D' hsub hchain' (m - x0) hle
        have hx0S : x0 ∉ S := fun h => (Finset.mem_erase.mp (hS h)).1 rfl
        refine ⟨insert x0 S, ?_, ?_⟩
        · exact Finset.insert_subset hx0D (hS.trans (Finset.erase_subset _ _))
        · rw [Finset.sum_insert hx0S, hSsum]
          omega

/-- For a practical number, each divisor is at most one more than the sum of the smaller
divisors. -/
lemma chain_of_practical {n : ℕ} (hn : Practical n) :
    ∀ x ∈ n.divisors, x ≤ 1 + ∑ y ∈ n.divisors.filter (fun y => y < x), y := by
  obtain ⟨hn0, hrep⟩ := hn
  intro x hx
  by_contra hcon
  push_neg at hcon
  set S := ∑ y ∈ n.divisors.filter (fun y => y < x), y with hSdef
  have hxn : x ≤ n := Nat.le_of_dvd hn0 (Nat.mem_divisors.mp hx).1
  obtain ⟨T, hT, hTsum⟩ := hrep (1 + S) (by omega)
  have hTsub : T ⊆ n.divisors.filter (fun y => y < x) := by
    intro y hy
    refine Finset.mem_filter.mpr ⟨hT hy, ?_⟩
    have : y ≤ ∑ d ∈ T, d := Finset.single_le_sum (f := fun d => d) (fun i _ => Nat.zero_le i) hy
    omega
  have : (1 : ℕ) + S ≤ S := by
    rw [← hTsum]
    exact Finset.sum_le_sum_of_subset hTsub
  omega

/-- Every `m` up to the sum of divisors of a practical number `n` is a sum of distinct
divisors of `n`. -/
lemma exists_subset_sum_of_practical {n : ℕ} (hn : Practical n) (m : ℕ)
    (hm : m ≤ ∑ y ∈ n.divisors, y) : ∃ S ⊆ n.divisors, ∑ d ∈ S, d = m :=
  exists_subset_sum_of_chain n.divisors (chain_of_practical hn) m hm

lemma self_le_sum_divisors {n : ℕ} (hn : 0 < n) : n ≤ ∑ y ∈ n.divisors, y :=
  Finset.single_le_sum (f := fun d => d) (fun i _ => Nat.zero_le i)
    (Nat.mem_divisors_self n hn.ne')

/-- Stewart's lemma: if `n` is practical and `1 ≤ d ≤ σ(n) + 1`, then `n * d` is practical. -/
lemma practical_mul {n d : ℕ} (hn : Practical n) (hd : 0 < d)
    (hdle : d ≤ 1 + ∑ y ∈ n.divisors, y) : Practical (n * d) := by
  obtain ⟨hn0, hrep⟩ := hn
  refine ⟨Nat.mul_pos hn0 hd, ?_⟩
  intro m hm
  have hqle : m / d ≤ n := by
    calc m / d ≤ (n * d) / d := Nat.div_le_div_right hm
    _ = n := Nat.mul_div_cancel _ hd
  obtain ⟨S1, hS1, hsum1⟩ := hrep (m / d) hqle
  have hrle : m % d ≤ ∑ y ∈ n.divisors, y := by
    have := Nat.mod_lt m hd
    omega
  obtain ⟨S2, hS2, hsum2⟩ := exists_subset_sum_of_practical ⟨hn0, hrep⟩ (m % d) hrle
  have hS1pos : ∀ e ∈ S1, 1 ≤ e := by
    intro e he
    have he' := Nat.mem_divisors.mp (hS1 he)
    refine Nat.one_le_iff_ne_zero.mpr ?_
    rintro rfl
    exact absurd (Nat.eq_zero_of_zero_dvd he'.1) hn0.ne'
  have hdisj : Disjoint (S1.image (fun e => d * e)) S2 := by
    rw [Finset.disjoint_left]
    intro u hu hu2
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hu
    have h1 : d ≤ d * e := Nat.le_mul_of_pos_right d (hS1pos e he)
    have h2 : d * e ≤ ∑ y ∈ S2, y :=
      Finset.single_le_sum (f := fun y => y) (fun i _ => Nat.zero_le i) hu2
    rw [hsum2] at h2
    have := Nat.mod_lt m hd
    omega
  refine ⟨(S1.image (fun e => d * e)) ∪ S2, ?_, ?_⟩
  · intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hu
      have he' := Nat.mem_divisors.mp (hS1 he)
      refine Nat.mem_divisors.mpr ⟨?_, (Nat.mul_pos hn0 hd).ne'⟩
      obtain ⟨k, hk⟩ := he'.1
      exact ⟨k, by rw [hk]; ring⟩
    · have hu' := Nat.mem_divisors.mp (hS2 hu)
      exact Nat.mem_divisors.mpr ⟨hu'.1.trans (Dvd.intro d rfl), (Nat.mul_pos hn0 hd).ne'⟩
  · rw [Finset.sum_union hdisj, Finset.sum_image (by
      intro a _ b _ hab
      exact Nat.eq_of_mul_eq_mul_left hd hab), hsum2, ← Finset.mul_sum, hsum1]
    exact Nat.div_add_mod m d

lemma practical_one : Practical 1 := by
  refine ⟨one_pos, ?_⟩
  intro m hm
  interval_cases m
  · exact ⟨∅, by simp⟩
  · exact ⟨{1}, by simp⟩

lemma practical_two_pow (a : ℕ) : Practical (2 ^ a) := by
  induction a with
  | zero => simpa using practical_one
  | succ a ih =>
    have h1 : (1 : ℕ) ≤ 2 ^ a := Nat.one_le_two_pow
    have h2 : 2 ^ a ≤ ∑ y ∈ (2 ^ a : ℕ).divisors, y := self_le_sum_divisors (by positivity)
    have h := practical_mul ih (d := 2) (by norm_num) (by omega)
    rwa [show 2 ^ a * 2 = 2 ^ (a + 1) by ring] at h

lemma practical_two_mul_three_pow (b : ℕ) : Practical (2 * 3 ^ b) := by
  induction b with
  | zero =>
    have h := practical_mul practical_one (d := 2) (by norm_num) (by simp)
    simpa using h
  | succ b ih =>
    have h1 : (1 : ℕ) ≤ 3 ^ b := Nat.one_le_pow _ _ (by norm_num)
    have h2 : 2 * 3 ^ b ≤ ∑ y ∈ (2 * 3 ^ b : ℕ).divisors, y := self_le_sum_divisors (by positivity)
    have h := practical_mul ih (d := 3) (by norm_num) (by omega)
    rwa [show 2 * 3 ^ b * 3 = 2 * 3 ^ (b + 1) by ring] at h

/-- Between `2 ^ a / 4` and `2 ^ a` there is always a power of `3`. -/
lemma exists_pow_three_between (a : ℕ) : ∃ b, 3 ^ b ≤ 2 ^ a ∧ 2 ^ a ≤ 4 * 3 ^ b := by
  induction a with
  | zero => exact ⟨0, by norm_num⟩
  | succ a ih =>
    obtain ⟨b, hb1, hb2⟩ := ih
    by_cases h : 2 ^ (a + 1) ≤ 4 * 3 ^ b
    · refine ⟨b, ?_, h⟩
      rw [pow_succ]; omega
    · refine ⟨b + 1, ?_, ?_⟩
      · rw [pow_succ, pow_succ]; omega
      · rw [pow_succ, pow_succ]; omega

/-- The key construction: for every `K` there is a practical `n > K` with `n + 2` practical. -/
lemma exists_practical_twin_gt (K : ℕ) :
    ∃ n, K < n ∧ Practical n ∧ Practical (n + 2) := by
  obtain ⟨b, hb1, hb2⟩ := exists_pow_three_between (K + 1)
  set a := K + 1 with hadef
  set M : ℕ := 3 ^ b with hMdef
  have hM0 : 0 < M := by positivity
  haveI : NeZero M := ⟨hM0.ne'⟩
  have hcop : Nat.Coprime (2 ^ a) M := by
    rw [hMdef]
    exact Nat.Coprime.pow _ _ (by norm_num)
  -- pick `t ∈ [1, M]` with `2 ^ a * t ≡ -2 [MOD M]`
  set x : ZMod M := (-2) * ((2 ^ a : ℕ) : ZMod M)⁻¹ with hxdef
  set t : ℕ := if x.val = 0 then M else x.val with htdef
  have hxt : ((t : ℕ) : ZMod M) = x := by
    by_cases h : x.val = 0
    · have hx0 : x = 0 := by
        have hv := ZMod.natCast_val (n := M) (R := ZMod M) x
        rw [h] at hv
        simpa [ZMod.cast_id] using hv.symm
      simp [htdef, hx0]
    · simp only [htdef, h, if_false]
      simp [ZMod.natCast_val, ZMod.cast_id]
  have ht1 : 1 ≤ t := by
    by_cases h : x.val = 0
    · simp only [htdef, h, if_true]; omega
    · simp only [htdef, h, if_false]; omega
  have ht2 : t ≤ M := by
    by_cases h : x.val = 0
    · simp [htdef, h]
    · simp only [htdef, h, if_false]
      exact le_of_lt (ZMod.val_lt x)
  set N : ℕ := 2 ^ a * t with hNdef
  have hNpos : 0 < N := by positivity
  have hMdvd : M ∣ N + 2 := by
    rw [← ZMod.natCast_eq_zero_iff]
    have hinv : ((2 ^ a : ℕ) : ZMod M) * ((2 ^ a : ℕ) : ZMod M)⁻¹ = 1 :=
      ZMod.coe_mul_inv_eq_one _ hcop
    have : ((N + 2 : ℕ) : ZMod M) = ((2 ^ a : ℕ) : ZMod M) * x + 2 := by
      rw [hNdef]; push_cast [hxt]; ring
    rw [this, hxdef]
    calc ((2 ^ a : ℕ) : ZMod M) * (-2 * ((2 ^ a : ℕ) : ZMod M)⁻¹) + 2
        = -2 * (((2 ^ a : ℕ) : ZMod M) * ((2 ^ a : ℕ) : ZMod M)⁻¹) + 2 := by ring
      _ = 0 := by rw [hinv]; ring
  have h2dvd : 2 ∣ N + 2 := by
    have h : (2 : ℕ) ∣ N := by
      rw [hNdef, hadef]
      exact Dvd.dvd.mul_right (dvd_pow_self 2 (Nat.succ_ne_zero K)) t
    omega
  have hcop2 : Nat.Coprime 2 M := by
    rw [hMdef]
    exact Nat.Coprime.pow_right _ (by norm_num)
  obtain ⟨s, hs⟩ : (2 * M) ∣ N + 2 := hcop2.mul_dvd_of_dvd_of_dvd h2dvd hMdvd
  have hs1 : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with rfl | h
    · omega
    · exact h
  have h2a : 2 ^ a = 2 * 2 ^ K := by rw [hadef, pow_succ]; ring
  have hsbound : s ≤ 2 ^ K + 1 := by
    have hNle : N ≤ 2 ^ a * M := by
      rw [hNdef]; exact Nat.mul_le_mul_left _ ht2
    have hkey : 2 * M * s ≤ 2 * M * (2 ^ K + 1) := by
      have h1 : 2 ^ a * M + 2 ≤ 2 * M * (2 ^ K + 1) := by
        rw [h2a]
        have : (2 : ℕ) ≤ 2 * M := by omega
        nlinarith [hM0]
      omega
    exact Nat.le_of_mul_le_mul_left hkey (by positivity)
  refine ⟨N, ?_, ?_, ?_⟩
  · have h1 : K < 2 ^ a := by
      rw [hadef]
      exact lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ K))
    have h2 : 2 ^ a ≤ N := by
      rw [hNdef]
      exact Nat.le_mul_of_pos_right _ ht1
    omega
  · refine practical_mul (practical_two_pow a) (by omega) ?_
    have h2 : 2 ^ a ≤ ∑ y ∈ (2 ^ a : ℕ).divisors, y := self_le_sum_divisors (by positivity)
    omega
  · rw [hs]
    refine practical_mul (practical_two_mul_three_pow b) (by omega) ?_
    have h2 : 2 * M ≤ ∑ y ∈ (2 * M : ℕ).divisors, y := self_le_sum_divisors (by positivity)
    have h3 : 2 ^ K ≤ 2 * M := by omega
    omega

/-- **Practical twin infinitude**: there are infinitely many `n` such that both `n` and `n + 2`
are practical numbers. -/
theorem PracticalTwinInfinitude : {n : ℕ | Practical n ∧ Practical (n + 2)}.Infinite := by
  refine Set.infinite_of_forall_exists_gt ?_
  intro K
  obtain ⟨n, hK, h1, h2⟩ := exists_practical_twin_gt K
  exact ⟨n, ⟨h1, h2⟩, hK⟩

end Brockian.PracticalNumbers

