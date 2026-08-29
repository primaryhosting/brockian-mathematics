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

namespace Brockian.PracticalNumbers

/-- A natural number `n` is *practical* if it is positive and every `t ≤ n` can be written
as a sum of distinct divisors of `n`. -/
def Practical (n : ℕ) : Prop :=
  0 < n ∧ ∀ t ≤ n, ∃ S ⊆ n.divisors, ∑ d ∈ S, d = t

/-- `Reach D B` says every `t ≤ B` is a sum of a subset of `D`. -/
def Reach (D : Finset ℕ) (B : ℕ) : Prop :=
  ∀ t ≤ B, ∃ S ⊆ D, ∑ d ∈ S, d = t

theorem Reach.mono {D D' : Finset ℕ} {B : ℕ} (h : Reach D B) (hDD : D ⊆ D') : Reach D' B := by
  intro t ht
  obtain ⟨S, hS, hsum⟩ := h t ht
  exact ⟨S, hS.trans hDD, hsum⟩

/-- Adding a new element `x`, larger than everything in `D` but at most `B + 1`,
extends the reach from `B` to `B + x`. -/
theorem Reach.step {D : Finset ℕ} {B x : ℕ} (h : Reach D B) (hx : x ≤ B + 1)
    (hlt : ∀ y ∈ D, y < x) : Reach (insert x D) (B + x) := by
  intro t ht
  by_cases hcase : t ≤ B
  · obtain ⟨S, hS, hsum⟩ := h t hcase
    exact ⟨S, hS.trans (Finset.subset_insert _ _), hsum⟩
  · push_neg at hcase
    obtain ⟨S, hS, hsum⟩ := h (t - x) (by omega)
    have hxS : x ∉ S := fun hmem => absurd (hlt x (hS hmem)) (lt_irrefl x)
    refine ⟨insert x S, Finset.insert_subset_insert _ hS, ?_⟩
    rw [Finset.sum_insert hxS, hsum]
    omega

/-- Every divisor of a positive number is at most that number. -/
theorem le_of_mem_divisors {n y : ℕ} (hy : y ∈ n.divisors) : y ≤ n :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hy).2) (Nat.mem_divisors.mp hy).1

/-- Main multiplication criterion: if the divisors of `n` reach `B`, with `n ≤ B`,
then `n * k` is practical for every `0 < k ≤ B + 1`. -/
theorem practical_mul {n B k : ℕ} (hn : 0 < n) (hR : Reach n.divisors B) (hnB : n ≤ B)
    (hk : 0 < k) (hkB : k ≤ B + 1) : Practical (n * k) := by
  refine ⟨Nat.mul_pos hn hk, ?_⟩
  intro t ht
  have hqk : t / k ≤ n := by
    by_contra hcon
    push_neg at hcon
    have h1 : n * k < (t / k) * k := (Nat.mul_lt_mul_right hk).mpr hcon
    have h2 : (t / k) * k ≤ t := Nat.div_mul_le_self t k
    omega
  obtain ⟨Sq, hSq, hsumq⟩ := hR (t / k) (le_trans hqk hnB)
  obtain ⟨Sr, hSr, hsumr⟩ := hR (t % k) (by have := Nat.mod_lt t hk; omega)
  have hinj : Set.InjOn (fun d => k * d) Sq := by
    intro x _ y _ hxy
    exact Nat.eq_of_mul_eq_mul_left hk hxy
  set A : Finset ℕ := Sq.image (fun d => k * d) with hA
  have hsumA : ∑ d ∈ A, d = k * (t / k) := by
    rw [hA, Finset.sum_image (fun x hx y hy hxy => hinj hx hy hxy)]
    rw [← Finset.mul_sum, hsumq]
  have hdisj : Disjoint Sr A := by
    rw [Finset.disjoint_right]
    intro x hxA hxSr
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hxA
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors (hSq hd)
    have hkx : k ≤ k * d := Nat.le_mul_of_pos_right k hd1
    have hle : k * d ≤ ∑ y ∈ Sr, y :=
      Finset.single_le_sum (f := fun y => y) (fun i _ => Nat.zero_le i) hxSr
    rw [hsumr] at hle
    have := Nat.mod_lt t hk
    omega
  refine ⟨Sr ∪ A, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · have hd := Nat.mem_divisors.mp (hSr hx)
      exact Nat.mem_divisors.mpr ⟨hd.1.trans ⟨k, rfl⟩, by positivity⟩
    · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
      have hdn := (Nat.mem_divisors.mp (hSq hd)).1
      refine Nat.mem_divisors.mpr ⟨?_, by positivity⟩
      obtain ⟨c, rfl⟩ := hdn
      exact ⟨c, by ring⟩
  · rw [Finset.sum_union hdisj, hsumr, hsumA]
    exact Nat.mod_add_div t k

/-- The divisors `{1, 2, …, 2^a}` reach `2^(a+1) - 1`. -/
theorem reach_two_pow (a : ℕ) :
    ∃ D : Finset ℕ, D ⊆ (2 ^ a).divisors ∧ Reach D (2 ^ (a + 1) - 1) := by
  induction a with
  | zero =>
    refine ⟨{1}, by simp, ?_⟩
    intro t ht
    norm_num at ht
    interval_cases t
    · exact ⟨∅, by simp, by simp⟩
    · exact ⟨{1}, by simp, by simp⟩
  | succ a ih =>
    obtain ⟨D, hD, hR⟩ := ih
    have hpos : (0:ℕ) < 2 ^ a := by positivity
    have hstep : Reach (insert (2 ^ (a + 1)) D) (2 ^ (a + 1) - 1 + 2 ^ (a + 1)) := by
      refine hR.step ?_ ?_
      · have : (1:ℕ) ≤ 2 ^ (a + 1) := Nat.one_le_two_pow
        omega
      · intro y hy
        have h1 : y ≤ 2 ^ a := le_of_mem_divisors (hD hy)
        have h2 : (2:ℕ) ^ (a + 1) = 2 * 2 ^ a := by ring
        omega
    refine ⟨insert (2 ^ (a + 1)) D, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Nat.mem_divisors.mpr ⟨dvd_rfl, by positivity⟩
      · have hd := Nat.mem_divisors.mp (hD hx)
        exact Nat.mem_divisors.mpr ⟨hd.1.trans (pow_dvd_pow 2 (Nat.le_succ a)), by positivity⟩
    · have heq : 2 ^ (a + 1) - 1 + 2 ^ (a + 1) = 2 ^ (a + 1 + 1) - 1 := by
        have h0 : (2:ℕ) ^ (a + 1 + 1) = 2 ^ (a + 1) + 2 ^ (a + 1) := by ring
        have h1 : (1:ℕ) ≤ 2 ^ (a + 1) := Nat.one_le_two_pow
        omega
      rwa [heq] at hstep

/-- The bound reached by the divisors `{3^i, 2·3^i : i ≤ j}` of `2 * 3^j`. -/
def T : ℕ → ℕ
  | 0 => 3
  | (j + 1) => T j + 3 ^ (j + 1) + 2 * 3 ^ (j + 1)

theorem pow_le_T (j : ℕ) : 3 ^ (j + 1) ≤ T j := by
  induction j with
  | zero => simp [T]
  | succ j ih =>
    have h : (3:ℕ) ^ (j + 1 + 1) = 3 * 3 ^ (j + 1) := by ring
    simp only [T]
    omega

theorem two_mul_pow_le_T (j : ℕ) : 2 * 3 ^ j ≤ T j := by
  have h := pow_le_T j
  have h2 : (3:ℕ) ^ (j + 1) = 3 * 3 ^ j := by ring
  omega

/-- The divisors `{3^i, 2·3^i : i ≤ j}` of `2 * 3^j` reach `T j`. -/
theorem reach_two_mul_three_pow (j : ℕ) :
    ∃ D : Finset ℕ, D ⊆ (2 * 3 ^ j).divisors ∧ Reach D (T j) := by
  induction j with
  | zero =>
    refine ⟨{1, 2}, ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> exact Nat.mem_divisors.mpr ⟨by norm_num, by norm_num⟩
    intro t ht
    simp only [T] at ht
    interval_cases t
    · exact ⟨∅, by simp, by simp⟩
    · exact ⟨{1}, by simp, by simp⟩
    · exact ⟨{2}, by simp, by simp⟩
    · exact ⟨{1, 2}, by simp, by norm_num⟩
  | succ j ih =>
    obtain ⟨D, hD, hR⟩ := ih
    have h3 : (0:ℕ) < 3 ^ j := by positivity
    have hpow : (3:ℕ) ^ (j + 1) = 3 * 3 ^ j := by ring
    have hT := pow_le_T j
    have hstep1 : Reach (insert (3 ^ (j + 1)) D) (T j + 3 ^ (j + 1)) := by
      refine hR.step (by omega) ?_
      intro y hy
      have h1 : y ≤ 2 * 3 ^ j := le_of_mem_divisors (hD hy)
      omega
    have hstep2 : Reach (insert (2 * 3 ^ (j + 1)) (insert (3 ^ (j + 1)) D))
        (T j + 3 ^ (j + 1) + 2 * 3 ^ (j + 1)) := by
      refine hstep1.step (by omega) ?_
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · omega
      · have h1 : y ≤ 2 * 3 ^ j := le_of_mem_divisors (hD hy)
        omega
    refine ⟨insert (2 * 3 ^ (j + 1)) (insert (3 ^ (j + 1)) D), ?_, hstep2⟩
    intro x hx
    have hne : 2 * 3 ^ (j + 1) ≠ 0 := by positivity
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Nat.mem_divisors.mpr ⟨dvd_rfl, hne⟩
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Nat.mem_divisors.mpr ⟨⟨2, by ring⟩, hne⟩
    · have hd := Nat.mem_divisors.mp (hD hx)
      exact Nat.mem_divisors.mpr ⟨hd.1.trans ⟨3, by rw [hpow]; ring⟩, hne⟩

/-- Every positive `x` has a power of three in the window `[x, 3x)`. -/
theorem exists_pow_three_window (x : ℕ) (hx : 0 < x) : ∃ j, x ≤ 3 ^ j ∧ 3 ^ j < 3 * x := by
  classical
  have hex : ∃ j, x ≤ 3 ^ j := ⟨x, le_of_lt (Nat.lt_pow_self (by norm_num))⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
  · rw [h]
    have h0 : (3:ℕ) ^ 0 = 1 := pow_zero 3
    omega
  · have hmin := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
    push_neg at hmin
    have heq : (3:ℕ) ^ (Nat.find hex) = 3 * 3 ^ (Nat.find hex - 1) := by
      conv_lhs => rw [show Nat.find hex = (Nat.find hex - 1) + 1 by omega]
      ring
    omega

/-- **Practical twin infinitude**: there are infinitely many `n` such that both `n` and `n + 2`
are practical numbers. -/
theorem PracticalTwinInfinitude :
    ∀ M : ℕ, ∃ n : ℕ, M < n ∧ Practical n ∧ Practical (n + 2) := by
  intro M
  set a : ℕ := M + 2 with ha
  have haM : M < 2 ^ a := by
    have h1 : M < 2 ^ M := Nat.lt_two_pow_self
    have h2 : (2:ℕ) ^ M ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hapow : (2:ℕ) ^ a = 2 * 2 ^ (M + 1) := by rw [ha]; ring
  obtain ⟨j, hj1, hj2⟩ := exists_pow_three_window (2 ^ (M + 1)) (by positivity)
  have h3pos : (0:ℕ) < 3 ^ j := by positivity
  have h2pow : (1:ℕ) ≤ 2 ^ (M + 1) := Nat.one_le_two_pow
  have h2le : (2:ℕ) ≤ 2 ^ (M + 1) := by
    have h2 : (2:ℕ) ^ 1 ≤ 2 ^ (M + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa using h2
  have hjbig : 3 ≤ 3 ^ j := by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · exfalso; norm_num at hj1
    · have h3 : (3:ℕ) ^ 1 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj
      simpa using h3
  have hco : Nat.Coprime (2 ^ a) (3 ^ j) := Nat.Coprime.pow _ _ (by norm_num)
  set cr := Nat.chineseRemainder hco 0 (3 ^ j - 2) with hcr
  have hlt : (cr : ℕ) < 2 ^ a * 3 ^ j :=
    Nat.chineseRemainder_lt_mul hco 0 (3 ^ j - 2) (by positivity) (by positivity)
  have hmod1 : (cr : ℕ) % 2 ^ a = 0 := by
    have h := cr.2.1
    unfold Nat.ModEq at h
    simpa using h
  have hmod2 : (cr : ℕ) % 3 ^ j = 3 ^ j - 2 := by
    have h := cr.2.2
    unfold Nat.ModEq at h
    rw [h, Nat.mod_eq_of_lt (by omega)]
  set N : ℕ := (cr : ℕ) with hN
  have hNdvd : 2 ^ a ∣ N := Nat.dvd_of_mod_eq_zero hmod1
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · exfalso
      rw [h] at hmod2
      simp at hmod2
      omega
    · exact h
  have hN3 : 3 ^ j ∣ N + 2 := by
    have h1 : N % 3 ^ j + 3 ^ j * (N / 3 ^ j) = N := Nat.mod_add_div N (3 ^ j)
    rw [hmod2] at h1
    refine ⟨N / 3 ^ j + 1, ?_⟩
    have h2 : 3 ^ j * (N / 3 ^ j + 1) = 3 ^ j * (N / 3 ^ j) + 3 ^ j := by ring
    omega
  obtain ⟨m, hm⟩ := hNdvd
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, Nat.mul_zero] at hm; omega
    · exact h
  have hmlt : m < 3 ^ j := by
    have h2a : (0:ℕ) < 2 ^ a := by positivity
    by_contra hcon
    push_neg at hcon
    have h1 : 2 ^ a * 3 ^ j ≤ 2 ^ a * m := Nat.mul_le_mul_left _ hcon
    omega
  have hprac1 : Practical N := by
    obtain ⟨D, hD, hR⟩ := reach_two_pow a
    rw [hm]
    refine practical_mul (by positivity) (hR.mono hD) ?_ hmpos ?_
    · have h1 : (2:ℕ) ^ (a + 1) = 2 * 2 ^ a := by ring
      have h2 : (1:ℕ) ≤ 2 ^ a := Nat.one_le_two_pow
      omega
    · have h1 : (2:ℕ) ^ (a + 1) = 2 * 2 ^ a := by ring
      have h2 : (1:ℕ) ≤ 2 ^ a := Nat.one_le_two_pow
      omega
  have hN2even : 2 ∣ N + 2 := by
    have h1 : (2:ℕ) ∣ 2 ^ a := dvd_pow_self 2 (by omega)
    exact Nat.dvd_add (h1.trans ⟨m, hm⟩) dvd_rfl
  have hco2 : Nat.Coprime 2 (3 ^ j) := Nat.Coprime.pow_right _ (by norm_num)
  have hdvd2 : 2 * 3 ^ j ∣ N + 2 := Nat.Coprime.mul_dvd_of_dvd_of_dvd hco2 hN2even hN3
  obtain ⟨k, hk⟩ := hdvd2
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, Nat.mul_zero] at hk; omega
    · exact h
  have hTj := two_mul_pow_le_T j
  have hkle : k ≤ T j + 1 := by
    have hbig : 2 ^ a ≤ 2 * 3 ^ j := by omega
    have h1 : N + 2 ≤ 2 * 3 ^ j * 3 ^ j + 2 := by
      have h0 : 2 ^ a * 3 ^ j ≤ 2 * 3 ^ j * 3 ^ j := Nat.mul_le_mul_right _ hbig
      omega
    have h2 : 2 * 3 ^ j * k ≤ 2 * 3 ^ j * (T j + 1) := by
      have h4 : 3 ^ j + 1 ≤ T j + 1 := by omega
      have h5 : 2 * 3 ^ j * (3 ^ j + 1) ≤ 2 * 3 ^ j * (T j + 1) := Nat.mul_le_mul_left _ h4
      have h6 : 2 * 3 ^ j * (3 ^ j + 1) = 2 * 3 ^ j * 3 ^ j + 2 * 3 ^ j := by ring
      omega
    exact Nat.le_of_mul_le_mul_left h2 (by positivity)
  have hprac2 : Practical (N + 2) := by
    obtain ⟨D, hD, hR⟩ := reach_two_mul_three_pow j
    rw [hk]
    exact practical_mul (by positivity) (hR.mono hD) hTj hkpos hkle
  refine ⟨N, ?_, hprac1, hprac2⟩
  have h1 : 2 ^ a ≤ N := Nat.le_of_dvd hNpos ⟨m, hm⟩
  omega

/-- Restatement: the set of `n` with `n` and `n + 2` both practical is infinite. -/
theorem setOf_practical_twins_infinite :
    {n : ℕ | Practical n ∧ Practical (n + 2)}.Infinite := by
  refine Set.infinite_of_forall_exists_gt ?_
  intro M
  obtain ⟨n, hn, h1, h2⟩ := PracticalTwinInfinitude M
  exact ⟨n, ⟨h1, h2⟩, hn⟩

/-- Sanity check: the notion of practicality is not vacuous; `5` is not practical. -/
example : ¬ Practical 5 := by
  rintro ⟨-, h⟩
  obtain ⟨S, hS, hsum⟩ := h 4 (by norm_num)
  have hd : (5:ℕ).divisors = {1, 5} := by decide
  rw [hd] at hS
  have hmem : S ∈ ({1, 5} : Finset ℕ).powerset := Finset.mem_powerset.mpr hS
  fin_cases hmem <;> simp_all

end Brockian.PracticalNumbers

