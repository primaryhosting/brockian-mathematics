/-!
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
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
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.PracticalNumbers

open Finset

/-- A natural number `n` is *practical* if it is positive and every `m ≤ n` can be written
as a sum of distinct divisors of `n`. -/
def Practical (n : ℕ) : Prop :=
  0 < n ∧ ∀ m ≤ n, ∃ S ⊆ n.divisors, ∑ x ∈ S, x = m

/-- A finite set `D` of naturals is *complete* if every `m` up to the total sum of `D`
is a sum of a subset of `D`. -/
def Complete (D : Finset ℕ) : Prop :=
  ∀ m ≤ ∑ x ∈ D, x, ∃ S ⊆ D, ∑ x ∈ S, x = m

section Step

variable (D : Finset ℕ) (k : ℕ)

lemma sum_union_image (hk : 0 < k)
    (hdisj : Disjoint D (D.image (fun d => k * d))) :
    ∑ x ∈ (D ∪ D.image (fun d => k * d)), x = (1 + k) * ∑ x ∈ D, x := by
  rw [Finset.sum_union hdisj,
    Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hk h), ← Finset.mul_sum]
  ring

/-- The key scaling step: if `D` is complete and `k ≤ (∑ D) + 1`, then `D ∪ k • D`
is complete (provided the two pieces are disjoint). -/
lemma complete_step (hk : 0 < k) (hD : Complete D) (hle : k ≤ (∑ x ∈ D, x) + 1)
    (hdisj : Disjoint D (D.image (fun d => k * d))) :
    Complete (D ∪ D.image (fun d => k * d)) := by
  intro m hm
  rw [sum_union_image D k hk hdisj] at hm
  set S := ∑ x ∈ D, x with hS
  obtain ⟨a, b, ha, hb, hab⟩ : ∃ a b, a ≤ S ∧ b ≤ S ∧ m = k * a + b := by
    rcases le_or_gt (m / k) S with h | h
    · refine ⟨m / k, m % k, h, ?_, (Nat.div_add_mod m k).symm⟩
      have := Nat.mod_lt m hk
      omega
    · have hkS : (S + 1) * k ≤ m := (Nat.le_div_iff_mul_le hk).mp h
      have e1 : (S + 1) * k = k * S + k := by ring
      have e2 : (1 + k) * S = S + k * S := by ring
      exact ⟨S, m - k * S, le_rfl, by omega, by omega⟩
  obtain ⟨A, hA, hAsum⟩ := hD a ha
  obtain ⟨B, hB, hBsum⟩ := hD b hb
  have hAsub : A.image (fun d => k * d) ⊆ D.image (fun d => k * d) :=
    Finset.image_subset_image hA
  have hdisj' : Disjoint (A.image (fun d => k * d)) B := hdisj.symm.mono hAsub hB
  refine ⟨A.image (fun d => k * d) ∪ B, ?_, ?_⟩
  · exact Finset.union_subset (hAsub.trans Finset.subset_union_right)
      (hB.trans Finset.subset_union_left)
  · rw [Finset.sum_union hdisj',
      Finset.sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hk h), ← Finset.mul_sum,
      hAsum, hBsum, hab]

end Step

/-! ### Powers of two are practical -/

lemma image_range_subset (k : ℕ) :
    (Finset.range k).image (fun j => 2 ^ j) ⊆ (Finset.range (k + 1)).image (fun j => 2 ^ j) := by
  intro x hx
  simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
  obtain ⟨j, hj, rfl⟩ := hx
  exact ⟨j, by omega, rfl⟩

lemma pow_two_rep (k : ℕ) :
    ∀ m < 2 ^ k, ∃ S ⊆ (Finset.range k).image (fun j => 2 ^ j), ∑ x ∈ S, x = m := by
  induction k with
  | zero =>
      intro m hm
      refine ⟨∅, by simp, ?_⟩
      simp only [Finset.sum_empty]
      simpa using (by omega : m = 0).symm
  | succ k ih =>
      intro m hm
      rcases lt_or_ge m (2 ^ k) with h | h
      · obtain ⟨S, hS, hSsum⟩ := ih m h
        exact ⟨S, hS.trans (image_range_subset k), hSsum⟩
      · have hm' : m - 2 ^ k < 2 ^ k := by
          have : (2:ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
          omega
        obtain ⟨S, hS, hSsum⟩ := ih _ hm'
        have hlt : ∀ x ∈ S, x < 2 ^ k := by
          intro x hx
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (hS hx)
          exact Nat.pow_lt_pow_right (by norm_num) (Finset.mem_range.mp hj)
        have hnot : 2 ^ k ∉ S := fun hmem => absurd (hlt _ hmem) (lt_irrefl _)
        refine ⟨insert (2 ^ k) S, ?_, ?_⟩
        · refine Finset.insert_subset ?_ (hS.trans (image_range_subset k))
          exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_self k), rfl⟩
        · rw [Finset.sum_insert hnot, hSsum]
          omega

lemma practical_two_pow (k : ℕ) : Practical (2 ^ k) := by
  refine ⟨Nat.two_pow_pos k, ?_⟩
  intro m hm
  rcases lt_or_eq_of_le hm with h | h
  · obtain ⟨S, hS, hSsum⟩ := pow_two_rep k m h
    refine ⟨S, ?_, hSsum⟩
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (hS hx)
    exact Nat.mem_divisors.mpr ⟨pow_dvd_pow 2 (le_of_lt (Finset.mem_range.mp hj)),
      (Nat.two_pow_pos k).ne'⟩
  · exact ⟨{2 ^ k}, by simp [Nat.mem_divisors], by simpa using h.symm⟩

/-! ### The family `N i = 2 ^ (2 ^ i + 1) - 2` -/

/-- Fermat-type factors `F i = 2 ^ (2 ^ i) + 1`. -/
def F (i : ℕ) : ℕ := 2 ^ (2 ^ i) + 1

/-- `N i = 2 * (2 ^ (2 ^ i) - 1)`, defined recursively as `2 * F 0 * F 1 * ... * F (i-1)`. -/
def N : ℕ → ℕ
  | 0 => 2
  | (i + 1) => N i * F i

/-- Explicit sets of divisors witnessing practicality of `N i`. -/
def Dset : ℕ → Finset ℕ
  | 0 => {1, 2}
  | (i + 1) => Dset i ∪ (Dset i).image (fun d => F i * d)

lemma F_pos (i : ℕ) : 0 < F i := by
  simp only [F]
  positivity

lemma two_le_pow (i : ℕ) : 2 ≤ 2 ^ (2 ^ i) := by
  calc (2:ℕ) = 2 ^ 1 := by norm_num
  _ ≤ 2 ^ (2 ^ i) := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow

lemma N_add_two (i : ℕ) : N i + 2 = 2 * 2 ^ (2 ^ i) := by
  induction i with
  | zero => norm_num [N]
  | succ i ih =>
      have hsq : (2:ℕ) ^ (2 ^ (i + 1)) = 2 ^ (2 ^ i) * 2 ^ (2 ^ i) := by
        rw [← pow_add]
        congr 1
        ring
      have hN : N (i + 1) = N i * (2 ^ (2 ^ i) + 1) := rfl
      rw [hN, hsq]
      nlinarith [ih]

lemma N_pos (i : ℕ) : 0 < N i := by
  have := N_add_two i
  have := two_le_pow i
  omega

lemma F_le_N_succ (i : ℕ) : F i ≤ N i + 1 := by
  have h := N_add_two i
  have h2 := two_le_pow i
  simp only [F]
  omega

lemma F_not_dvd_N (i : ℕ) : ¬ (F i ∣ N i) := by
  intro hdvd
  have h := N_add_two i
  have h2 := two_le_pow i
  have heven : 2 ∣ 2 ^ (2 ^ i) := dvd_pow_self 2 (Nat.two_pow_pos i).ne'
  have he : N i + 4 = 2 * F i := by simp only [F]; omega
  have hF4 : F i ∣ N i + 4 := ⟨2, by omega⟩
  have h4 : F i ∣ 4 := (Nat.dvd_add_right hdvd).mp hF4
  have hle : F i ≤ 4 := Nat.le_of_dvd (by norm_num) h4
  have hF3 : F i = 3 := by
    simp only [F] at hle ⊢
    omega
  rw [hF3] at h4
  omega

lemma Dset_dvd (i : ℕ) : ∀ d ∈ Dset i, d ∣ N i := by
  induction i with
  | zero =>
      intro d hd
      fin_cases hd <;> simp [N]
  | succ i ih =>
      intro d hd
      have hN : N (i + 1) = N i * F i := rfl
      rw [hN]
      rcases Finset.mem_union.mp hd with h | h
      · exact (ih d h).trans (dvd_mul_right _ _)
      · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h
        have hd' : F i * e ∣ F i * N i := mul_dvd_mul_left _ (ih e he)
        rwa [mul_comm (F i) (N i)] at hd'

lemma Dset_disjoint (i : ℕ) : Disjoint (Dset i) ((Dset i).image (fun d => F i * d)) := by
  rw [Finset.disjoint_right]
  rintro x hx hx'
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
  exact F_not_dvd_N i ((Dvd.intro e rfl).trans (Dset_dvd i _ hx'))

lemma N_le_sum_Dset (i : ℕ) : N i ≤ ∑ x ∈ Dset i, x := by
  induction i with
  | zero => norm_num [N, Dset]
  | succ i ih =>
      show N (i + 1) ≤ ∑ x ∈ (Dset i ∪ (Dset i).image (fun d => F i * d)), x
      rw [sum_union_image (Dset i) (F i) (F_pos i) (Dset_disjoint i)]
      have hN : N (i + 1) = N i * F i := rfl
      rw [hN]
      calc N i * F i ≤ (∑ x ∈ Dset i, x) * F i := Nat.mul_le_mul_right _ ih
        _ ≤ (1 + F i) * ∑ x ∈ Dset i, x := by nlinarith [Nat.zero_le (∑ x ∈ Dset i, x)]

lemma Dset_complete (i : ℕ) : Complete (Dset i) := by
  induction i with
  | zero =>
      intro m hm
      have hsum : ∑ x ∈ (Dset 0), x = 3 := by decide
      rw [hsum] at hm
      interval_cases m
      · exact ⟨∅, by simp, by simp⟩
      · exact ⟨{1}, by decide, by decide⟩
      · exact ⟨{2}, by decide, by decide⟩
      · exact ⟨{1, 2}, by decide, by decide⟩
  | succ i ih =>
      show Complete (Dset i ∪ (Dset i).image (fun d => F i * d))
      refine complete_step (Dset i) (F i) (F_pos i) ih ?_ (Dset_disjoint i)
      have h1 := F_le_N_succ i
      have h2 := N_le_sum_Dset i
      omega

lemma practical_N (i : ℕ) : Practical (N i) := by
  refine ⟨N_pos i, ?_⟩
  intro m hm
  obtain ⟨S, hS, hSsum⟩ := Dset_complete i m (hm.trans (N_le_sum_Dset i))
  exact ⟨S, fun x hx => Nat.mem_divisors.mpr ⟨Dset_dvd i x (hS hx), (N_pos i).ne'⟩, hSsum⟩

lemma practical_N_add_two (i : ℕ) : Practical (N i + 2) := by
  have h : N i + 2 = 2 ^ (2 ^ i + 1) := by rw [N_add_two i, pow_succ]; ring
  rw [h]
  exact practical_two_pow _

lemma lt_N (B : ℕ) : B < N B := by
  have h := N_add_two B
  have h2 := two_le_pow B
  have hB : B < 2 ^ B := Nat.lt_two_pow_self
  have hmono : (2:ℕ) ^ B ≤ 2 ^ (2 ^ B) := Nat.pow_le_pow_right (by norm_num) hB.le
  omega

/-- **Practical twin infinitude**: there are infinitely many `n` such that both `n` and `n + 2`
are practical numbers. -/
theorem PracticalTwinInfinitude :
    {n : ℕ | Practical n ∧ Practical (n + 2)}.Infinite :=
  Set.infinite_of_forall_exists_gt fun B =>
    ⟨N B, ⟨practical_N B, practical_N_add_two B⟩, lt_N B⟩

end Brockian.PracticalNumbers

