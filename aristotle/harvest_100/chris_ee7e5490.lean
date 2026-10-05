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

/-!
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

A natural number `n` is *practical* if every `m ≤ n` is a sum of distinct divisors of `n`.
We prove that there are infinitely many `n` such that `n` and `n + 2` are both practical.

The proof is completely explicit.  Two families of practical numbers are established by
direct subset-sum arguments:

* `2 ^ k * u` is practical whenever `u` is odd and `u ≤ 2 ^ (k+1)`;
* `2 * 3 ^ b * t` is practical whenever `t` is odd, prime to `3`, and `t ≤ 3 ^ b`.

Given `b ≥ 1`, put `s = Nat.log 2 (3 ^ b)`, so `2 ^ s ≤ 3 ^ b < 2 ^ (s+1)`, and let `M` be the
Chinese-remainder solution of `M ≡ 0 [MOD 3 ^ b]`, `M ≡ -1 [MOD 2 ^ s]` with `M < 3 ^ b * 2 ^ s`.
Then `2 * M` lies in the second family and `2 * M + 2 = 2 * (M + 1)` lies in the first, so
`(2 * M, 2 * M + 2)` is a twin pair of practical numbers of size at least `2 * 3 ^ b`.
-/

namespace Brockian.PracticalNumbers

open Finset

/-- A positive integer `n` is *practical* if every `m ≤ n` can be written as a sum of
distinct divisors of `n`. -/
def Practical (n : ℕ) : Prop :=
  0 < n ∧ ∀ m ≤ n, ∃ S ⊆ n.divisors, ∑ d ∈ S, d = m

/-- To prove `n` practical it suffices to exhibit a set `D` of divisors of `n` from which
every `m ≤ n` can be assembled. -/
lemma practical_of_subset {n : ℕ} (hn : 0 < n) (D : Finset ℕ) (hD : D ⊆ n.divisors)
    (h : ∀ m ≤ n, ∃ S ⊆ D, ∑ d ∈ S, d = m) : Practical n := by
  refine ⟨hn, fun m hm => ?_⟩
  obtain ⟨S, hS, hsum⟩ := h m hm
  exact ⟨S, hS.trans hD, hsum⟩

/-! ### Powers of two -/

/-- The divisors `1, 2, 4, …, 2^k`. -/
def pow2set (k : ℕ) : Finset ℕ := (range (k + 1)).image (fun i => 2 ^ i)

lemma pow2set_mono {k : ℕ} : pow2set k ⊆ pow2set (k + 1) := by
  exact Finset.image_subset_image (Finset.range_subset.mpr (by omega))

lemma mem_pow2set_le {k d : ℕ} (hd : d ∈ pow2set k) : d ≤ 2 ^ k := by
  simp only [pow2set, Finset.mem_image, Finset.mem_range] at hd
  obtain ⟨i, hi, rfl⟩ := hd
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

lemma mem_pow2set_dvd {k d : ℕ} (hd : d ∈ pow2set k) : d ∣ 2 ^ k := by
  simp only [pow2set, Finset.mem_image, Finset.mem_range] at hd
  obtain ⟨i, hi, rfl⟩ := hd
  exact pow_dvd_pow 2 (by omega)

lemma repr_pow2 (k : ℕ) : ∀ m < 2 ^ (k + 1), ∃ S ⊆ pow2set k, ∑ d ∈ S, d = m := by
  induction k with
  | zero =>
    intro m hm
    norm_num at hm
    interval_cases m
    · exact ⟨∅, by simp, by simp⟩
    · exact ⟨{1}, by simp [pow2set], by simp⟩
  | succ k ih =>
    intro m hm
    by_cases h : m < 2 ^ (k + 1)
    · obtain ⟨S, hS, hsum⟩ := ih m h
      exact ⟨S, hS.trans pow2set_mono, hsum⟩
    · push_neg at h
      have hsplit : (2 : ℕ) ^ (k + 2) = 2 ^ (k + 1) + 2 ^ (k + 1) := by ring
      have h1 : m - 2 ^ (k + 1) < 2 ^ (k + 1) := by omega
      obtain ⟨S, hS, hsum⟩ := ih _ h1
      have hnot : 2 ^ (k + 1) ∉ S := by
        intro hmem
        have h2 := mem_pow2set_le (hS hmem)
        have h3 : (2 : ℕ) ^ k < 2 ^ (k + 1) := by
          exact Nat.pow_lt_pow_right one_lt_two (by omega)
        omega
      refine ⟨insert (2 ^ (k + 1)) S, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · simp only [pow2set, Finset.mem_image, Finset.mem_range]
          exact ⟨k + 1, by omega, rfl⟩
        · exact pow2set_mono (hS hx)
      · rw [Finset.sum_insert hnot, hsum]
        omega

/-! ### The divisors of `2 * 3 ^ b` -/

/-- The divisors `3^j` and `2 * 3^j` for `j ≤ b`. -/
def three2set (b : ℕ) : Finset ℕ :=
  (range (b + 1)).image (fun j => 3 ^ j) ∪ (range (b + 1)).image (fun j => 2 * 3 ^ j)

/-- The sum of the elements of `three2set b`, defined recursively. -/
def sigma3 : ℕ → ℕ
  | 0 => 3
  | b + 1 => sigma3 b + 3 ^ (b + 2)

lemma three_pow_le_sigma3 (b : ℕ) : 3 ^ (b + 1) ≤ sigma3 b := by
  induction b with
  | zero => simp [sigma3]
  | succ b ih =>
    have : (3 : ℕ) ^ (b + 2) ≤ sigma3 b + 3 ^ (b + 2) := by omega
    simpa [sigma3] using this

lemma two_mul_three_pow_le_sigma3 (b : ℕ) : 2 * 3 ^ b ≤ sigma3 b := by
  have h := three_pow_le_sigma3 b
  have : (3 : ℕ) ^ (b + 1) = 3 * 3 ^ b := by ring
  omega

lemma three2set_mono {b : ℕ} : three2set b ⊆ three2set (b + 1) := by
  apply Finset.union_subset_union <;>
    exact Finset.image_subset_image (Finset.range_subset.mpr (by omega))

lemma mem_three2set_le {b d : ℕ} (hd : d ∈ three2set b) : d ≤ 2 * 3 ^ b := by
  simp only [three2set, Finset.mem_union, Finset.mem_image, Finset.mem_range] at hd
  rcases hd with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · have : (3 : ℕ) ^ j ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · have : (3 : ℕ) ^ j ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

lemma mem_three2set_dvd {b d : ℕ} (hd : d ∈ three2set b) : d ∣ 2 * 3 ^ b := by
  simp only [three2set, Finset.mem_union, Finset.mem_image, Finset.mem_range] at hd
  rcases hd with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · exact Dvd.dvd.mul_left (pow_dvd_pow 3 (by omega)) 2
  · exact Nat.mul_dvd_mul_left 2 (pow_dvd_pow 3 (by omega))

lemma three_pow_succ_notMem {b : ℕ} : (3 : ℕ) ^ (b + 1) ∉ three2set b := by
  intro hmem
  have h := mem_three2set_le hmem
  have : (3 : ℕ) ^ (b + 1) = 3 * 3 ^ b := by ring
  have hpos : 0 < (3 : ℕ) ^ b := Nat.pow_pos (by norm_num) b
  omega

lemma two_mul_three_pow_succ_notMem {b : ℕ} : 2 * (3 : ℕ) ^ (b + 1) ∉ three2set b := by
  intro hmem
  have h := mem_three2set_le hmem
  have : (3 : ℕ) ^ (b + 1) = 3 * 3 ^ b := by ring
  have hpos : 0 < (3 : ℕ) ^ b := Nat.pow_pos (by norm_num) b
  omega

lemma repr_three (b : ℕ) : ∀ m ≤ sigma3 b, ∃ S ⊆ three2set b, ∑ d ∈ S, d = m := by
  induction b with
  | zero =>
    intro m hm
    simp only [sigma3] at hm
    have h2 : three2set 0 = {1, 2} := by decide
    interval_cases m
    · exact ⟨∅, by simp, by simp⟩
    · exact ⟨{1}, by rw [h2]; intro x hx; simp at hx; simp [hx], by simp⟩
    · exact ⟨{2}, by rw [h2]; intro x hx; simp at hx; simp [hx], by simp⟩
    · exact ⟨{1, 2}, by rw [h2], by decide⟩
  | succ b ih =>
    intro m hm
    have hσ := three_pow_le_sigma3 b
    have hpow : (3 : ℕ) ^ (b + 2) = 3 * 3 ^ (b + 1) := by ring
    simp only [sigma3] at hm
    by_cases h1 : m ≤ sigma3 b
    · obtain ⟨S, hS, hsum⟩ := ih m h1
      exact ⟨S, hS.trans three2set_mono, hsum⟩
    push_neg at h1
    by_cases h2 : m ≤ sigma3 b + 3 ^ (b + 1)
    · -- use the divisor `3 ^ (b+1)`
      obtain ⟨S, hS, hsum⟩ := ih (m - 3 ^ (b + 1)) (by omega)
      have hnot : (3 : ℕ) ^ (b + 1) ∉ S := fun hmem => three_pow_succ_notMem (hS hmem)
      refine ⟨insert (3 ^ (b + 1)) S, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · simp only [three2set, Finset.mem_union, Finset.mem_image, Finset.mem_range]
          exact Or.inl ⟨b + 1, by omega, rfl⟩
        · exact three2set_mono (hS hx)
      · rw [Finset.sum_insert hnot, hsum]
        omega
    push_neg at h2
    by_cases h3 : m ≤ sigma3 b + 2 * 3 ^ (b + 1)
    · -- use the divisor `2 * 3 ^ (b+1)`
      obtain ⟨S, hS, hsum⟩ := ih (m - 2 * 3 ^ (b + 1)) (by omega)
      have hnot : 2 * (3 : ℕ) ^ (b + 1) ∉ S := fun hmem => two_mul_three_pow_succ_notMem (hS hmem)
      refine ⟨insert (2 * 3 ^ (b + 1)) S, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · simp only [three2set, Finset.mem_union, Finset.mem_image, Finset.mem_range]
          exact Or.inr ⟨b + 1, by omega, rfl⟩
        · exact three2set_mono (hS hx)
      · rw [Finset.sum_insert hnot, hsum]
        omega
    push_neg at h3
    -- use both `3 ^ (b+1)` and `2 * 3 ^ (b+1)`
    obtain ⟨S, hS, hsum⟩ := ih (m - 3 * 3 ^ (b + 1)) (by omega)
    have hnot1 : (3 : ℕ) ^ (b + 1) ∉ S := fun hmem => three_pow_succ_notMem (hS hmem)
    have hnot2 : 2 * (3 : ℕ) ^ (b + 1) ∉ S := fun hmem => two_mul_three_pow_succ_notMem (hS hmem)
    have hpos : 0 < (3 : ℕ) ^ (b + 1) := Nat.pow_pos (by norm_num) _
    have hne : (3 : ℕ) ^ (b + 1) ≠ 2 * 3 ^ (b + 1) := by omega
    refine ⟨insert (3 ^ (b + 1)) (insert (2 * 3 ^ (b + 1)) S), ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · simp only [three2set, Finset.mem_union, Finset.mem_image, Finset.mem_range]
        exact Or.inl ⟨b + 1, by omega, rfl⟩
      rcases Finset.mem_insert.mp hx with rfl | hx
      · simp only [three2set, Finset.mem_union, Finset.mem_image, Finset.mem_range]
        exact Or.inr ⟨b + 1, by omega, rfl⟩
      · exact three2set_mono (hS hx)
    · rw [Finset.sum_insert (by simp [hne, hnot1]), Finset.sum_insert hnot2, hsum]
      omega

/-! ### The gluing lemma -/

/-- If `D` is a set of divisors of `c` rich enough to represent all `A ≤ c` and all `B < t`,
and `t * d ≠ d'` for all `d, d' ∈ D`, then `c * t` is practical. -/
lemma practical_glue {c t : ℕ} (D : Finset ℕ) (hc : 0 < c) (ht : 0 < t)
    (hD : ∀ d ∈ D, d ∣ c)
    (hA : ∀ A ≤ c, ∃ S ⊆ D, ∑ d ∈ S, d = A)
    (hB : ∀ B < t, ∃ S ⊆ D, ∑ d ∈ S, d = B)
    (hcross : ∀ d ∈ D, ∀ d' ∈ D, t * d ≠ d') :
    Practical (c * t) := by
  have hct : 0 < c * t := Nat.mul_pos hc ht
  refine ⟨hct, fun m hm => ?_⟩
  have hAle : m / t ≤ c := by
    have h := Nat.div_le_div_right (c := t) hm
    rwa [Nat.mul_div_cancel _ ht] at h
  obtain ⟨S1, hS1, hsum1⟩ := hA (m / t) hAle
  obtain ⟨S2, hS2, hsum2⟩ := hB (m % t) (Nat.mod_lt _ ht)
  have hinj : Set.InjOn (fun d => t * d) S1 := by
    intro x _ y _ h
    exact Nat.eq_of_mul_eq_mul_left ht h
  have hdisj : Disjoint (S1.image (fun d => t * d)) S2 := by
    rw [Finset.disjoint_left]
    intro x hx hx2
    simp only [Finset.mem_image] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    exact hcross d (hS1 hd) _ (hS2 hx2) rfl
  refine ⟨(S1.image (fun d => t * d)) ∪ S2, ?_, ?_⟩
  · intro x hx
    rw [Nat.mem_divisors]
    refine ⟨?_, by omega⟩
    rcases Finset.mem_union.mp hx with hx | hx
    · simp only [Finset.mem_image] at hx
      obtain ⟨d, hd, rfl⟩ := hx
      rw [mul_comm c t]
      exact Nat.mul_dvd_mul_left t (hD d (hS1 hd))
    · exact Dvd.dvd.mul_right (hD x (hS2 hx)) t
  · rw [Finset.sum_union hdisj, Finset.sum_image hinj, ← Finset.mul_sum, hsum1, hsum2]
    exact Nat.div_add_mod m t

/-! ### Two families of practical numbers -/

/-- If `u` is odd and `u ≤ 2 ^ (k+1)` then `2 ^ k * u` is practical. -/
lemma practical_two_pow_mul_odd {k u : ℕ} (hu : Odd u) (hle : u ≤ 2 ^ (k + 1)) :
    Practical (2 ^ k * u) := by
  have hupos : 0 < u := hu.pos
  rcases eq_or_lt_of_le hupos with h1 | h1
  · -- `u = 1`: a power of two
    have hu1 : u = 1 := by omega
    subst hu1
    rw [mul_one]
    refine practical_of_subset (Nat.pow_pos (by norm_num) k) (pow2set k) ?_ ?_
    · intro d hd
      rw [Nat.mem_divisors]
      exact ⟨mem_pow2set_dvd hd, by positivity⟩
    · intro m hm
      exact repr_pow2 k m (by
        have : (2 : ℕ) ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right one_lt_two (by omega)
        omega)
  · -- `u > 1`
    have hcross : ∀ d ∈ pow2set k, ∀ d' ∈ pow2set k, u * d ≠ d' := by
      intro d hd d' hd' heq
      simp only [pow2set, Finset.mem_image, Finset.mem_range] at hd hd'
      obtain ⟨i, _, rfl⟩ := hd
      obtain ⟨j, _, rfl⟩ := hd'
      have hdvd : u ∣ 2 ^ j := ⟨2 ^ i, by omega⟩
      obtain ⟨m, _, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp at h1
      · have : (2 : ℕ) ∣ 2 ^ m := dvd_pow_self 2 (by omega)
        rw [Nat.odd_iff] at hu
        omega
    have := practical_glue (c := 2 ^ k) (t := u) (pow2set k)
      (Nat.pow_pos (by norm_num) k) hupos
      (fun d hd => mem_pow2set_dvd hd)
      (fun A hA => repr_pow2 k A (by
        have : (2 : ℕ) ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right one_lt_two (by omega)
        omega))
      (fun B hB => repr_pow2 k B (by omega))
      hcross
    exact this

/-- If `t` is odd, prime to `3`, and `t ≤ 3 ^ b`, then `2 * 3 ^ b * t` is practical. -/
lemma practical_two_three_pow_mul {b t : ℕ} (hodd : Odd t) (h3 : ¬ (3 ∣ t))
    (hle : t ≤ 3 ^ b) : Practical (2 * 3 ^ b * t) := by
  have htpos : 0 < t := hodd.pos
  have hcpos : 0 < 2 * 3 ^ b := by positivity
  have hσ := two_mul_three_pow_le_sigma3 b
  rcases eq_or_lt_of_le htpos with h1 | h1
  · -- `t = 1`
    have ht1 : t = 1 := by omega
    subst ht1
    rw [mul_one]
    refine practical_of_subset hcpos (three2set b) ?_ ?_
    · intro d hd
      rw [Nat.mem_divisors]
      exact ⟨mem_three2set_dvd hd, by omega⟩
    · intro m hm
      exact repr_three b m (by omega)
  · -- `t > 1`
    have hcross : ∀ d ∈ three2set b, ∀ d' ∈ three2set b, t * d ≠ d' := by
      intro d hd d' hd' heq
      have hdvd : t ∣ 2 * 3 ^ b := dvd_trans ⟨d, by omega⟩ (mem_three2set_dvd hd')
      have hcop2 : Nat.Coprime t 2 := by
        rw [Nat.coprime_two_right_iff_odd]
        exact hodd
      have hdvd3 : t ∣ 3 ^ b := (Nat.Coprime.dvd_of_dvd_mul_left hcop2 hdvd)
      obtain ⟨m, _, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd3
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp at h1
      · exact h3 (dvd_pow_self 3 (by omega))
    exact practical_glue (c := 2 * 3 ^ b) (t := t) (three2set b) hcpos htpos
      (fun d hd => mem_three2set_dvd hd)
      (fun A hA => repr_three b A (by omega))
      (fun B hB => repr_three b B (by omega))
      hcross

/-! ### Extracting the exact power of a prime -/

lemma exists_factor_pow {p : ℕ} (hp : 1 < p) :
    ∀ M : ℕ, 0 < M → ∃ e t : ℕ, M = p ^ e * t ∧ ¬ p ∣ t := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    intro hM
    by_cases h : p ∣ M
    · obtain ⟨M', rfl⟩ := h
      have hM' : 0 < M' := by
        rcases Nat.eq_zero_or_pos M' with rfl | h'
        · simp at hM
        · exact h'
      have hlt : M' < p * M' := by nlinarith
      obtain ⟨e, t, he, ht⟩ := ih M' hlt hM'
      exact ⟨e + 1, t, by rw [he]; ring, ht⟩
    · exact ⟨0, M, by simp, h⟩

lemma le_of_pow_dvd {p e b t : ℕ} (hp : 0 < p) (ht : ¬ p ∣ t) (h : p ^ b ∣ p ^ e * t) :
    b ≤ e := by
  by_contra hlt
  push_neg at hlt
  have h2 : p ^ (e + 1) ∣ p ^ e * t := dvd_trans (pow_dvd_pow p (by omega)) h
  rw [pow_succ] at h2
  exact ht ((mul_dvd_mul_iff_left (a := p ^ e) (by positivity)).mp h2)

/-! ### The construction -/

/-- Key construction: for every `b ≥ 1` there is `n ≥ 2 * 3 ^ b` such that `n` and `n + 2`
are both practical. -/
lemma exists_twin_practical_ge (b : ℕ) (hb : 1 ≤ b) :
    ∃ n : ℕ, 2 * 3 ^ b ≤ n ∧ Practical n ∧ Practical (n + 2) := by
  -- the two moduli
  have hP3 : 3 ≤ 3 ^ b := by
    calc (3 : ℕ) = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  have hPne : (3 : ℕ) ^ b ≠ 0 := by positivity
  set s := Nat.log 2 (3 ^ b) with hsdef
  have h2s : 2 ^ s ≤ 3 ^ b := Nat.pow_log_le_self 2 hPne
  have hPlt : (3 : ℕ) ^ b < 2 ^ (s + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hs1 : 1 ≤ s := Nat.log_pos (by norm_num) (by omega)
  have h2spos : 0 < (2 : ℕ) ^ s := Nat.pow_pos (by norm_num) s
  have hcop : Nat.Coprime (3 ^ b) (2 ^ s) := Nat.Coprime.pow (by norm_num)
  -- Chinese remainder
  obtain ⟨M, hM0, hM1⟩ := Nat.chineseRemainder hcop 0 (2 ^ s - 1)
  have hMlt : M < 3 ^ b * 2 ^ s :=
    Nat.chineseRemainder_lt_mul hcop 0 (2 ^ s - 1) hPne (by omega)
  have hdvd3 : (3 : ℕ) ^ b ∣ M := (Nat.modEq_zero_iff_dvd).mp hM0
  have hdvd2 : (2 : ℕ) ^ s ∣ M + 1 := by
    have h : M % 2 ^ s = (2 ^ s - 1) % 2 ^ s := hM1
    rw [Nat.mod_eq_of_lt (by omega)] at h
    have h2 : (M + 1) % 2 ^ s = ((M % 2 ^ s) + 1 % 2 ^ s) % 2 ^ s := Nat.add_mod M 1 (2 ^ s)
    rw [h, Nat.mod_eq_of_lt (by omega)] at h2
    have h3 : 2 ^ s - 1 + 1 = 2 ^ s := by omega
    rw [h3, Nat.mod_self] at h2
    exact (Nat.dvd_iff_mod_eq_zero _ _).mpr h2
  have hMpos : 0 < M := by
    rcases Nat.eq_zero_or_pos M with rfl | h
    · have : (2 : ℕ) ^ s ∣ 1 := by simpa using hdvd2
      have := Nat.le_of_dvd (by norm_num) this
      have : (2 : ℕ) ≤ 2 ^ s := by
        calc (2 : ℕ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs1
      omega
    · exact h
  have hModd : Odd M := by
    have h2 : (2 : ℕ) ∣ M + 1 := dvd_trans (dvd_pow_self 2 (by omega)) hdvd2
    rcases Nat.even_or_odd M with he | ho
    · exfalso
      rw [Nat.even_iff] at he
      omega
    · exact ho
  refine ⟨2 * M, ?_, ?_, ?_⟩
  · have := Nat.le_of_dvd hMpos hdvd3
    omega
  · -- `2 * M` is practical
    obtain ⟨e, t, hMe, ht3⟩ := exists_factor_pow (p := 3) (by norm_num) M hMpos
    have hbe : b ≤ e := le_of_pow_dvd (by norm_num) ht3 (hMe ▸ hdvd3)
    have h3b3e : (3 : ℕ) ^ b ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) hbe
    have htodd : Odd t := by
      rcases Nat.even_or_odd t with he' | ho
      · exfalso
        obtain ⟨r, hr⟩ := he'
        rw [Nat.odd_iff] at hModd
        rw [hMe, hr] at hModd
        omega
      · exact ho
    have htlt : t < 2 ^ s := by
      by_contra hcon
      push_neg at hcon
      have : (3 : ℕ) ^ e * 2 ^ s ≤ 3 ^ e * t := Nat.mul_le_mul_left _ hcon
      have h2 : (3 : ℕ) ^ b * 2 ^ s ≤ 3 ^ e * 2 ^ s := Nat.mul_le_mul_right _ h3b3e
      omega
    have htle : t ≤ 3 ^ e := by omega
    have hrw : 2 * M = 2 * 3 ^ e * t := by rw [hMe]; ring
    rw [hrw]
    exact practical_two_three_pow_mul htodd ht3 htle
  · -- `2 * M + 2 = 2 * (M + 1)` is practical
    have hK : 2 * M + 2 = 2 * (M + 1) := by ring
    have hKpos : 0 < 2 * (M + 1) := by omega
    obtain ⟨k, u, hKe, hu2⟩ := exists_factor_pow (p := 2) (by norm_num) (2 * (M + 1)) hKpos
    have hdvdK : (2 : ℕ) ^ (s + 1) ∣ 2 * (M + 1) := by
      rw [pow_succ, mul_comm ((2:ℕ)^s) 2]
      exact Nat.mul_dvd_mul_left 2 hdvd2
    have hsk : s + 1 ≤ k := le_of_pow_dvd (by norm_num) hu2 (hKe ▸ hdvdK)
    have huodd : Odd u := by
      rcases Nat.even_or_odd u with he' | ho
      · exact absurd he'.two_dvd hu2
      · exact ho
    have hule : u ≤ 2 ^ (k + 1) := by
      -- `2 ^ k * u = 2 * (M+1) ≤ 2 * 3 ^ b * 2 ^ s < 2 ^ (s+1) * 2 ^ (s+1) ≤ 2 ^ k * 2 ^ (s+1)`
      have h1 : (2 : ℕ) ^ k * u < 2 ^ (s + 1) * 2 ^ (s + 1) := by
        have hb1 : M + 1 ≤ 3 ^ b * 2 ^ s := by omega
        calc (2 : ℕ) ^ k * u = 2 * (M + 1) := hKe.symm
          _ ≤ 2 * (3 ^ b * 2 ^ s) := by omega
          _ < 2 * (2 ^ (s + 1) * 2 ^ s) := by
              have : (3 : ℕ) ^ b * 2 ^ s < 2 ^ (s + 1) * 2 ^ s :=
                (Nat.mul_lt_mul_right h2spos).mpr hPlt
              omega
          _ = 2 ^ (s + 1) * 2 ^ (s + 1) := by ring
      have h2 : (2 : ℕ) ^ (s + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hsk
      have h3 : (2 : ℕ) ^ k * u < 2 ^ k * 2 ^ (s + 1) := by
        calc (2 : ℕ) ^ k * u < 2 ^ (s + 1) * 2 ^ (s + 1) := h1
          _ ≤ 2 ^ k * 2 ^ (s + 1) := Nat.mul_le_mul_right _ h2
      have h4 : u < 2 ^ (s + 1) :=
        lt_of_mul_lt_mul_left h3 (Nat.zero_le _)
      have h5 : (2 : ℕ) ^ k ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [hK, hKe]
    exact practical_two_pow_mul_odd huodd hule

/-- **Practical twin infinitude**: there are infinitely many `n` such that both `n` and
`n + 2` are practical numbers. -/
theorem PracticalTwinInfinitude :
    ∀ N : ℕ, ∃ n : ℕ, N < n ∧ Practical n ∧ Practical (n + 2) := by
  intro N
  obtain ⟨n, hn, h1, h2⟩ := exists_twin_practical_ge (N + 1) (by omega)
  refine ⟨n, ?_, h1, h2⟩
  have h3 : N < 3 ^ N := Nat.lt_pow_self (by norm_num)
  have h4 : (3 : ℕ) ^ N ≤ 3 ^ (N + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end Brockian.PracticalNumbers

