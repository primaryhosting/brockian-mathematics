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
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Brockian.PracticalNumbers

/-!
## Overview

A positive integer `n` is *practical* if every `m ≤ n` is a sum of distinct divisors of `n`.
We prove that there are infinitely many `n` with `n` and `n + 2` both practical.

The construction: fix a large `a`, let `3 ^ b` be the largest power of `3` with `3 ^ b ≤ 2 ^ (a+1)`,
and let `s` be the representative in `[1, 3 ^ b)` of `-(2 ^ (a-1))⁻¹ mod 3 ^ b`.  Then

* `n = 2 ^ a * s` is practical because `s ≤ 3 ^ b ≤ 2 ^ (a+1) = σ(2 ^ a) + 1`;
* `n + 2 = 2 * (2 ^ (a-1) * s + 1)` where `3 ^ b` divides `2 ^ (a-1) * s + 1`, so writing
  `2 ^ (a-1) * s + 1 = 3 ^ b' * v` with `3 ∤ v` and `b' ≥ b`, we get `v ≤ 2 ^ (a-1) < 3 ^ (b'+1)`,
  which makes `2 * 3 ^ b' * v` practical.

Practicality of these two families is obtained from an explicit complete set of divisors
(`P2` for powers of two, `D3` for `2 * 3 ^ b`) together with a combination lemma
(`subsetSum_combine`), a constructive version of Stewart's criterion.
-/

/-- `SubsetSum D t` means `t` is the sum of a subset of the finite set `D`. -/
def SubsetSum (D : Finset ℕ) (t : ℕ) : Prop := ∃ S ⊆ D, ∑ d ∈ S, d = t

/-- A *practical* number: a positive integer `n` such that every `m ≤ n` is a sum of
distinct divisors of `n`. -/
def Practical (n : ℕ) : Prop := 0 < n ∧ ∀ m ≤ n, SubsetSum n.divisors m

/-! ## Basic facts about subset sums -/

lemma SubsetSum.mono {D D' : Finset ℕ} (h : D ⊆ D') {t : ℕ} (ht : SubsetSum D t) :
    SubsetSum D' t := by
  obtain ⟨S, hS, hsum⟩ := ht
  exact ⟨S, hS.trans h, hsum⟩

lemma practical_of_complete {n : ℕ} (hn : 0 < n) (D : Finset ℕ) (hD : D ⊆ n.divisors)
    (h : ∀ t ≤ n, SubsetSum D t) : Practical n :=
  ⟨hn, fun m hm => (h m hm).mono hD⟩

/-- Adding one new element to a set of which a subset sums to `t`. -/
lemma SubsetSum.insert_of {D : Finset ℕ} {x t : ℕ} (hx : x ∉ D) (h : SubsetSum D t) :
    SubsetSum (insert x D) (t + x) := by
  obtain ⟨S, hS, hsum⟩ := h
  refine ⟨insert x S, Finset.insert_subset_insert _ hS, ?_⟩
  rw [Finset.sum_insert (fun hmem => hx (hS hmem)), hsum, Nat.add_comm]

/-! ## The key combination lemma -/

/-- If every `t ≤ ∑ D` is a subset sum of `D`, if `w ≤ ∑ D + 1`, and if multiplication by `w`
maps `D` off of `D`, then every `t ≤ w * ∑ D` is a subset sum of `D ∪ w • D`. -/
lemma subsetSum_combine {D : Finset ℕ} {w t : ℕ}
    (hcomp : ∀ r ≤ ∑ d ∈ D, d, SubsetSum D r) (hw : 1 ≤ w) (hwS : w ≤ (∑ d ∈ D, d) + 1)
    (hcoll : ∀ d ∈ D, ∀ d' ∈ D, w * d ≠ d') (ht : t ≤ w * ∑ d ∈ D, d) :
    SubsetSum (D ∪ D.image (fun d => w * d)) t := by
  have hw0 : 0 < w := hw
  obtain ⟨S1, hS1, hq⟩ := hcomp (t / w) (by
    calc t / w ≤ (w * ∑ d ∈ D, d) / w := Nat.div_le_div_right ht
      _ = ∑ d ∈ D, d := Nat.mul_div_cancel_left _ hw0)
  obtain ⟨S2, hS2, hr⟩ := hcomp (t % w) (by
    have := Nat.mod_lt t hw0
    omega)
  have hinj : ∀ x ∈ S1, ∀ y ∈ S1, w * x = w * y → x = y := fun x _ y _ h =>
    Nat.eq_of_mul_eq_mul_left hw0 h
  have hdisj : Disjoint S2 (S1.image (fun d => w * d)) := by
    rw [Finset.disjoint_right]
    intro x hx hx2
    obtain ⟨d, hd, hdx⟩ := Finset.mem_image.mp hx
    exact hcoll d (hS1 hd) x (hS2 hx2) hdx
  refine ⟨S2 ∪ S1.image (fun d => w * d),
    Finset.union_subset_union hS2 (Finset.image_subset_image hS1), ?_⟩
  rw [Finset.sum_union hdisj, Finset.sum_image hinj, hr, ← Finset.mul_sum, hq]
  exact Nat.mod_add_div t w

/-- Practicality from a complete set of divisors. -/
lemma practical_of_completeSet {m : ℕ} (hm0 : 0 < m) (D : Finset ℕ) (hD : ∀ d ∈ D, d ∣ m)
    (hm : m ∈ D) (hcomp : ∀ t ≤ ∑ d ∈ D, d, SubsetSum D t) : Practical m := by
  have hmS : m ≤ ∑ d ∈ D, d := Finset.single_le_sum (fun i _ => Nat.zero_le i) hm
  refine practical_of_complete hm0 D (fun x hx => Nat.mem_divisors.mpr ⟨hD x hx, hm0.ne'⟩) ?_
  intro t ht
  exact hcomp t (ht.trans hmS)

/-- Practicality of `w * m` from a complete set of divisors of `m`. -/
lemma practical_of_combine {m w : ℕ} (hm0 : 0 < m) (D : Finset ℕ) (hD : ∀ d ∈ D, d ∣ m)
    (hm : m ∈ D) (hcomp : ∀ t ≤ ∑ d ∈ D, d, SubsetSum D t) (hw : 1 ≤ w)
    (hwS : w ≤ (∑ d ∈ D, d) + 1) (hcoll : ∀ d ∈ D, ∀ d' ∈ D, w * d ≠ d') :
    Practical (w * m) := by
  have hmS : m ≤ ∑ d ∈ D, d := Finset.single_le_sum (fun i _ => Nat.zero_le i) hm
  have hpos : 0 < w * m := Nat.mul_pos hw hm0
  refine practical_of_complete hpos (D ∪ D.image (fun d => w * d)) ?_ ?_
  · intro x hx
    rw [Finset.mem_union] at hx
    refine Nat.mem_divisors.mpr ⟨?_, hpos.ne'⟩
    rcases hx with hx | hx
    · exact (hD x hx).trans (dvd_mul_left m w)
    · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
      exact Nat.mul_dvd_mul_left w (hD d hd)
  · intro t ht
    exact subsetSum_combine hcomp hw hwS hcoll (ht.trans (Nat.mul_le_mul_left w hmS))

/-! ## Powers of two -/

/-- `P2 A = {1, 2, 4, …, 2^A}`. -/
def P2 : ℕ → Finset ℕ
  | 0 => {1}
  | (A + 1) => insert (2 ^ (A + 1)) (P2 A)

lemma P2_le {A x : ℕ} (hx : x ∈ P2 A) : x ≤ 2 ^ A := by
  induction A with
  | zero =>
    rw [P2] at hx
    simp only [Finset.mem_singleton] at hx
    simp [hx]
  | succ A ih =>
    rw [P2, Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact le_rfl
    · exact (ih hx).trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ A))

lemma P2_dvd {A x : ℕ} (hx : x ∈ P2 A) : x ∣ 2 ^ A := by
  induction A with
  | zero =>
    rw [P2] at hx
    simp only [Finset.mem_singleton] at hx
    simp [hx]
  | succ A ih =>
    rw [P2, Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact dvd_rfl
    · exact (ih hx).trans (pow_dvd_pow 2 (Nat.le_succ A))

lemma pow_mem_P2 (A : ℕ) : 2 ^ A ∈ P2 A := by
  cases A with
  | zero => simp [P2]
  | succ A => rw [P2]; exact Finset.mem_insert_self _ _

lemma pow_notMem_P2 (A : ℕ) : 2 ^ (A + 1) ∉ P2 A := by
  intro h
  have h1 := P2_le h
  have h2 : (2 : ℕ) ^ A < 2 ^ (A + 1) := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self A)
  omega

lemma sum_P2 (A : ℕ) : ∑ d ∈ P2 A, d = 2 ^ (A + 1) - 1 := by
  induction A with
  | zero => simp [P2]
  | succ A ih =>
    rw [P2, Finset.sum_insert (pow_notMem_P2 A), ih]
    have h1 : (1 : ℕ) ≤ 2 ^ (A + 1) := Nat.one_le_two_pow
    have h2 : (2 : ℕ) ^ (A + 1 + 1) = 2 ^ (A + 1) + 2 ^ (A + 1) := by
      rw [pow_succ]; ring
    omega

lemma subsetSum_P2 (A : ℕ) {t : ℕ} (h : t ≤ 2 ^ (A + 1) - 1) : SubsetSum (P2 A) t := by
  induction A generalizing t with
  | zero =>
    have ht : t ≤ 1 := by norm_num at h; omega
    interval_cases t
    · exact ⟨∅, by simp, by simp⟩
    · exact ⟨{1}, by simp [P2], by simp⟩
  | succ A ih =>
    by_cases hc : t ≤ 2 ^ (A + 1) - 1
    · exact (ih hc).mono (by rw [P2]; exact Finset.subset_insert _ _)
    · push_neg at hc
      have h2 : (2 : ℕ) ^ (A + 1 + 1) = 2 ^ (A + 1) + 2 ^ (A + 1) := by rw [pow_succ]; ring
      have h1 : (1 : ℕ) ≤ 2 ^ (A + 1) := Nat.one_le_two_pow
      have hle : t - 2 ^ (A + 1) ≤ 2 ^ (A + 1) - 1 := by omega
      have hres := (ih hle).insert_of (pow_notMem_P2 A)
      have heq : t - 2 ^ (A + 1) + 2 ^ (A + 1) = t := by omega
      rw [heq] at hres
      rw [P2]
      exact hres

/-! ## The sets `{1, 2, 3, 6, …, 3^b, 2·3^b}` -/

/-- `D3 b = {2^e * 3^j : e ≤ 1, j ≤ b}`. -/
def D3 : ℕ → Finset ℕ
  | 0 => {1, 2}
  | (b + 1) => insert (3 ^ (b + 1)) (insert (2 * 3 ^ (b + 1)) (D3 b))

lemma D3_le {b x : ℕ} (hx : x ∈ D3 b) : x ≤ 2 * 3 ^ b := by
  induction b with
  | zero =>
    rw [D3] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> norm_num
  | succ b ih =>
    rw [D3, Finset.mem_insert, Finset.mem_insert] at hx
    have hp : (3 : ℕ) ^ (b + 1) = 3 * 3 ^ b := by ring
    rcases hx with rfl | rfl | hx
    · omega
    · omega
    · have := ih hx
      omega

lemma D3_dvd {b x : ℕ} (hx : x ∈ D3 b) : x ∣ 2 * 3 ^ b := by
  induction b with
  | zero =>
    rw [D3] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> norm_num
  | succ b ih =>
    rw [D3, Finset.mem_insert, Finset.mem_insert] at hx
    rcases hx with rfl | rfl | hx
    · exact dvd_mul_left _ _
    · exact dvd_rfl
    · exact (ih hx).trans (Nat.mul_dvd_mul_left 2 (pow_dvd_pow 3 (Nat.le_succ b)))

lemma two_mul_pow_mem_D3 (b : ℕ) : 2 * 3 ^ b ∈ D3 b := by
  cases b with
  | zero => norm_num [D3]
  | succ b =>
    rw [D3]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

lemma sum_D3_succ (b : ℕ) :
    ∑ d ∈ D3 (b + 1), d = (∑ d ∈ D3 b, d) + 3 * 3 ^ (b + 1) := by
  have hp : (3 : ℕ) ^ (b + 1) = 3 * 3 ^ b := by ring
  have hpos : 0 < (3 : ℕ) ^ b := (by positivity)
  have h1 : 2 * 3 ^ (b + 1) ∉ D3 b := by
    intro h
    have := D3_le h
    omega
  have h2 : (3 : ℕ) ^ (b + 1) ∉ insert (2 * 3 ^ (b + 1)) (D3 b) := by
    intro h
    rw [Finset.mem_insert] at h
    rcases h with h | h
    · omega
    · have := D3_le h
      omega
  rw [D3, Finset.sum_insert h2, Finset.sum_insert h1]
  omega

lemma pow_le_sum_D3 (b : ℕ) : 3 ^ (b + 1) ≤ ∑ d ∈ D3 b, d := by
  induction b with
  | zero => norm_num [D3]
  | succ b ih =>
    rw [sum_D3_succ]
    have h1 : (3 : ℕ) ^ (b + 1 + 1) = 3 * 3 ^ (b + 1) := by ring
    omega

lemma subsetSum_D3 (b : ℕ) {t : ℕ} (h : t ≤ ∑ d ∈ D3 b, d) : SubsetSum (D3 b) t := by
  induction b generalizing t with
  | zero =>
    have hsum : ∑ d ∈ D3 0, d = 3 := by norm_num [D3]
    rw [hsum] at h
    interval_cases t
    · exact ⟨∅, by simp, by simp⟩
    · exact ⟨{1}, by norm_num [D3], by simp⟩
    · exact ⟨{2}, by norm_num [D3], by simp⟩
    · exact ⟨{1, 2}, by norm_num [D3], by norm_num⟩
  | succ b ih =>
    set p := (3 : ℕ) ^ (b + 1) with hp
    set Sm := ∑ d ∈ D3 b, d with hSm
    have hpS : p ≤ Sm := pow_le_sum_D3 b
    have hsum : ∑ d ∈ D3 (b + 1), d = Sm + 3 * p := sum_D3_succ b
    have h3pos : 0 < (3 : ℕ) ^ b := by positivity
    have hp3 : p = 3 * 3 ^ b := by rw [hp]; ring
    have hnot1 : 2 * p ∉ D3 b := by
      intro hmem
      have h1 := D3_le hmem
      omega
    have hnot2 : p ∉ insert (2 * p) (D3 b) := by
      intro hmem
      rw [Finset.mem_insert] at hmem
      rcases hmem with h1 | h1
      · omega
      · have := D3_le h1
        omega
    rw [hsum] at h
    have hstep : ∀ r ≤ Sm, SubsetSum (insert (2 * p) (D3 b)) r := fun r hr =>
      (ih hr).mono (Finset.subset_insert _ _)
    rw [D3]
    by_cases hc : t ≤ Sm
    · exact (hstep t hc).mono (Finset.subset_insert _ _)
    push_neg at hc
    by_cases hc2 : t ≤ Sm + p
    · -- use p
      have hres := (hstep (t - p) (by omega)).insert_of hnot2
      have heq : t - p + p = t := by omega
      rwa [heq] at hres
    push_neg at hc2
    by_cases hc3 : t ≤ Sm + 2 * p
    · -- use 2p
      have hres := ((ih (show t - 2 * p ≤ Sm by omega)).insert_of hnot1)
      have heq : t - 2 * p + 2 * p = t := by omega
      rw [heq] at hres
      exact hres.mono (Finset.subset_insert _ _)
    · -- use both p and 2p
      push_neg at hc3
      have hres := ((ih (show t - 3 * p ≤ Sm by omega)).insert_of hnot1).insert_of hnot2
      have heq : t - 3 * p + 2 * p + p = t := by omega
      rwa [heq] at hres

/-! ## Two families of practical numbers -/

/-- If `0 < s ≤ 2^(a+1)` then `2^a * s` is practical. -/
lemma practical_pow_two_mul : ∀ s : ℕ, 0 < s → ∀ a : ℕ, s ≤ 2 ^ (a + 1) →
    Practical (2 ^ a * s) := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro hs a hle
    rcases Nat.even_or_odd s with he | ho
    · obtain ⟨s', rfl⟩ := he
      have h1 : 0 < s' := by omega
      have h2 : s' ≤ 2 ^ (a + 1 + 1) := by
        have : (2 : ℕ) ^ (a + 1) ≤ 2 ^ (a + 1 + 1) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have hres := ih s' (by omega) h1 (a + 1) h2
      have heq : 2 ^ (a + 1) * s' = 2 ^ a * (s' + s') := by rw [pow_succ]; ring
      rwa [heq] at hres
    · have hsum := sum_P2 a
      have hcomp : ∀ t ≤ ∑ d ∈ P2 a, d, SubsetSum (P2 a) t := by
        intro t ht
        rw [hsum] at ht
        exact subsetSum_P2 a ht
      have hodd2 : ¬ 2 ∣ s := by
        obtain ⟨k, hk⟩ := ho
        omega
      by_cases h1 : 1 < s
      case neg =>
        have hs1 : s = 1 := by omega
        subst hs1
        rw [Nat.mul_one]
        exact practical_of_completeSet ((by positivity)) (P2 a)
          (fun d hd => P2_dvd hd) (pow_mem_P2 a) hcomp
      case pos =>
        have hcoll : ∀ d ∈ P2 a, ∀ d' ∈ P2 a, s * d ≠ d' := by
          intro d _ d' hd' heq
          have hdvd : s ∣ 2 ^ a := dvd_trans ⟨d, heq.symm⟩ (P2_dvd hd')
          obtain ⟨k, _, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
          rcases Nat.eq_zero_or_pos k with rfl | hk
          · simp at h1
          · exact hodd2 (dvd_pow_self 2 (by omega))
        have hres := practical_of_combine ((by positivity)) (P2 a)
          (fun d hd => P2_dvd hd) (pow_mem_P2 a) hcomp (by omega) (by omega) hcoll
        rwa [Nat.mul_comm] at hres

/-- If `v` is coprime to `6` and `v ≤ 3^(b+1)` then `2 * 3^b * v` is practical. -/
lemma practical_two_pow_three_mul {b v : ℕ} (hv : 0 < v) (h2 : ¬ 2 ∣ v) (h3 : ¬ 3 ∣ v)
    (hle : v ≤ 3 ^ (b + 1)) : Practical (2 * 3 ^ b * v) := by
  have hm0 : 0 < 2 * 3 ^ b := by positivity
  have hcomp : ∀ t ≤ ∑ d ∈ D3 b, d, SubsetSum (D3 b) t := fun t ht => subsetSum_D3 b ht
  have hsum : 3 ^ (b + 1) ≤ ∑ d ∈ D3 b, d := pow_le_sum_D3 b
  by_cases h1 : 1 < v
  case neg =>
    have hv1 : v = 1 := by omega
    subst hv1
    rw [Nat.mul_one]
    exact practical_of_completeSet hm0 (D3 b) (fun d hd => D3_dvd hd) (two_mul_pow_mem_D3 b) hcomp
  case pos =>
    have hcoll : ∀ d ∈ D3 b, ∀ d' ∈ D3 b, v * d ≠ d' := by
      intro d _ d' hd' heq
      have hdvd : v ∣ 2 * 3 ^ b := dvd_trans ⟨d, heq.symm⟩ (D3_dvd hd')
      have hc2 : Nat.Coprime v 2 := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2).symm
      have hc3 : Nat.Coprime v (3 ^ b) :=
        (((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3).symm).pow_right b
      have : v = 1 := (hc2.mul_right hc3).eq_one_of_dvd hdvd
      omega
    have hres := practical_of_combine hm0 (D3 b) (fun d hd => D3_dvd hd) (two_mul_pow_mem_D3 b)
      hcomp (by omega) (by omega) hcoll
    rwa [Nat.mul_comm] at hres

/-! ## The construction -/

/-- For every `N` there is a practical `n > N` with `n + 2` practical. -/
theorem exists_practical_twin_gt (N : ℕ) :
    ∃ n > N, Practical n ∧ Practical (n + 2) := by
  -- choose `a` large, and `b` maximal with `3 ^ b ≤ 2 ^ (a + 1)`
  set a := N + 3 with ha
  have ha2 : 2 ≤ a := by omega
  have hNa : N < 2 ^ a := lt_of_lt_of_le (by omega) (le_of_lt (Nat.lt_two_pow_self (n := a)))
  set b := Nat.log 3 (2 ^ (a + 1)) with hb
  have h2pos : (0 : ℕ) < 2 ^ (a + 1) := (by positivity)
  have h3le : (3 : ℕ) ^ 1 ≤ 2 ^ (a + 1) := by
    have : (2 : ℕ) ^ 3 ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at this ⊢
    omega
  have hb1 : 1 ≤ b := Nat.le_log_of_pow_le (by norm_num) h3le
  have hble : 3 ^ b ≤ 2 ^ (a + 1) := Nat.pow_log_le_self 3 h2pos.ne'
  have hblt : 2 ^ (a + 1) < 3 ^ (b + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hq1 : 1 < 3 ^ b := by
    calc (1 : ℕ) < 3 ^ 1 := by norm_num
      _ ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) hb1
  -- choose `s` with `2 ^ (a - 1) * s ≡ -1 mod 3 ^ b`
  have hcop : Nat.Coprime (2 ^ (a - 1)) (3 ^ b) := Nat.Coprime.pow _ _ (by decide)
  obtain ⟨mm, -, hmm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hq1
  set s := (mm * (3 ^ b - 1)) % 3 ^ b with hs
  have hs_lt : s < 3 ^ b := Nat.mod_lt _ (by omega)
  have hdvd : 3 ^ b ∣ 2 ^ (a - 1) * s + 1 := by
    have e1 : (2 ^ (a - 1) * mm) ≡ 1 [MOD 3 ^ b] := by
      unfold Nat.ModEq
      rw [hmm, Nat.mod_eq_of_lt hq1]
    have e2 : 2 ^ (a - 1) * s ≡ 2 ^ (a - 1) * (mm * (3 ^ b - 1)) [MOD 3 ^ b] :=
      Nat.ModEq.mul_left _ (Nat.mod_modEq _ _)
    have e3 : 2 ^ (a - 1) * (mm * (3 ^ b - 1)) = (2 ^ (a - 1) * mm) * (3 ^ b - 1) := by ring
    have e4 : (2 ^ (a - 1) * mm) * (3 ^ b - 1) ≡ 1 * (3 ^ b - 1) [MOD 3 ^ b] :=
      Nat.ModEq.mul_right _ e1
    have e5 : 2 ^ (a - 1) * s + 1 ≡ 1 * (3 ^ b - 1) + 1 [MOD 3 ^ b] :=
      ((e2.trans (e3 ▸ e4))).add_right 1
    have e6 : 1 * (3 ^ b - 1) + 1 = 3 ^ b := by omega
    rw [e6] at e5
    exact (Nat.modEq_zero_iff_dvd).mp (e5.trans ((Nat.modEq_zero_iff_dvd).mpr dvd_rfl))
  have hs_pos : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · rw [h0, Nat.mul_zero] at hdvd
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
    · exact h0
  refine ⟨2 ^ a * s, ?_, ?_, ?_⟩
  · calc N < 2 ^ a := hNa
      _ = 2 ^ a * 1 := by ring
      _ ≤ 2 ^ a * s := Nat.mul_le_mul_left _ hs_pos
  · exact practical_pow_two_mul s hs_pos a (by omega)
  · -- `n + 2 = 2 * u` with `u = 2 ^ (a - 1) * s + 1`
    set u := 2 ^ (a - 1) * s + 1 with hu
    have ha1 : a = (a - 1) + 1 := by omega
    have hpow : (2 : ℕ) ^ a = 2 * 2 ^ (a - 1) := by
      conv_lhs => rw [ha1]
      rw [pow_succ]
      ring
    have hn2 : 2 ^ a * s + 2 = 2 * u := by rw [hpow, hu]; ring
    have hu0 : u ≠ 0 := by positivity
    have hu_odd : ¬ 2 ∣ u := by
      have h2a : (2 : ℕ) ∣ 2 ^ (a - 1) * s :=
        Dvd.dvd.mul_right (dvd_pow_self 2 (by omega : a - 1 ≠ 0)) s
      obtain ⟨f, hf⟩ := h2a
      rw [hu]
      intro hcon
      obtain ⟨e, he⟩ := hcon
      omega
    -- extract the full power of `3`
    set b' := u.factorization 3 with hb'
    have hdvd' : (3 : ℕ) ^ b' ∣ u :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hu0).mpr le_rfl
    obtain ⟨v, huv'⟩ := hdvd'
    have huv : 3 ^ b' * v = u := huv'.symm
    have h3pos : (0 : ℕ) < 3 ^ b' := (by positivity)
    have hv0 : 0 < v := by
      rcases Nat.eq_zero_or_pos v with h0 | h0
      · rw [h0, Nat.mul_zero] at huv; exact absurd huv.symm hu0
      · exact h0
    have hv2 : ¬ 2 ∣ v := fun h => hu_odd (huv ▸ Dvd.dvd.mul_left h _)
    have hv3 : ¬ 3 ∣ v := by
      intro h
      obtain ⟨c, hc⟩ := h
      have hdd : (3 : ℕ) ^ (b' + 1) ∣ u := ⟨c, by rw [← huv, hc]; ring⟩
      have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hu0).mp hdd
      omega
    -- bound `v`
    have hbb' : b ≤ b' :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hu0).mp (hu ▸ hdvd)
    have hu_le : u ≤ 2 ^ (a - 1) * 3 ^ b := by
      have h1 : 1 ≤ (2 : ℕ) ^ (a - 1) := Nat.one_le_two_pow
      have h2 : 2 ^ (a - 1) * s ≤ 2 ^ (a - 1) * (3 ^ b - 1) :=
        Nat.mul_le_mul_left _ (by omega)
      have h3 : 2 ^ (a - 1) * (3 ^ b - 1) + 2 ^ (a - 1) = 2 ^ (a - 1) * 3 ^ b := by
        have : (3 : ℕ) ^ b - 1 + 1 = 3 ^ b := by omega
        calc 2 ^ (a - 1) * (3 ^ b - 1) + 2 ^ (a - 1)
            = 2 ^ (a - 1) * ((3 ^ b - 1) + 1) := by ring
          _ = 2 ^ (a - 1) * 3 ^ b := by rw [this]
      omega
    have hv_le : v ≤ 2 ^ (a - 1) := by
      have h1 : 3 ^ b' * v ≤ 2 ^ (a - 1) * 3 ^ b' := by
        calc 3 ^ b' * v = u := huv
          _ ≤ 2 ^ (a - 1) * 3 ^ b := hu_le
          _ ≤ 2 ^ (a - 1) * 3 ^ b' :=
              Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hbb')
      have h2 : 3 ^ b' * v ≤ 3 ^ b' * 2 ^ (a - 1) := by
        rw [Nat.mul_comm (3 ^ b') (2 ^ (a - 1))]
        exact h1
      exact Nat.le_of_mul_le_mul_left h2 h3pos
    have hv_le' : v ≤ 3 ^ (b' + 1) := by
      have h1 : (2 : ℕ) ^ (a - 1) ≤ 2 ^ (a + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : (3 : ℕ) ^ (b + 1) ≤ 3 ^ (b' + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hfinal : 2 ^ a * s + 2 = 2 * 3 ^ b' * v := by
      rw [hn2, ← huv]; ring
    rw [hfinal]
    exact practical_two_pow_three_mul hv0 hv2 hv3 hv_le'

/-! ## Sanity checks on the definition -/

/-- A decidable reformulation of `Practical`, used for sanity checks. -/
lemma practical_iff_powerset (n : ℕ) :
    Practical n ↔
      0 < n ∧ ∀ m ∈ Finset.range (n + 1), ∃ S ∈ n.divisors.powerset, ∑ d ∈ S, d = m := by
  constructor
  · rintro ⟨hn, h⟩
    refine ⟨hn, fun m hm => ?_⟩
    obtain ⟨S, hS, hsum⟩ := h m (by rw [Finset.mem_range] at hm; omega)
    exact ⟨S, Finset.mem_powerset.mpr hS, hsum⟩
  · rintro ⟨hn, h⟩
    refine ⟨hn, fun m hm => ?_⟩
    obtain ⟨S, hS, hsum⟩ := h m (Finset.mem_range.mpr (by omega))
    exact ⟨S, Finset.mem_powerset.mp hS, hsum⟩

example : Practical 6 := by rw [practical_iff_powerset]; decide
example : Practical 8 := by rw [practical_iff_powerset]; decide
example : Practical 16 := by rw [practical_iff_powerset]; decide
example : Practical 18 := by rw [practical_iff_powerset]; decide
example : ¬ Practical 5 := by rw [practical_iff_powerset]; decide
example : ¬ Practical 10 := by rw [practical_iff_powerset]; decide

-- the twin pair produced by the construction for `a = 4`
example : Practical 160 := practical_pow_two_mul 10 (by norm_num) 4 (by norm_num)
example : Practical 162 := by
  have := practical_two_pow_three_mul (b := 4) (v := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  norm_num at this
  exact this

/-- Main theorem: there are infinitely many `n` such that both `n` and `n + 2` are practical. -/
theorem PracticalTwinInfinitude : {n : ℕ | Practical n ∧ Practical (n + 2)}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨n, hn, h1, h2⟩ := exists_practical_twin_gt a
  exact ⟨n, ⟨h1, h2⟩, hn⟩

end Brockian.PracticalNumbers

