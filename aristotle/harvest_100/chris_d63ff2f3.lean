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
-- (Lean requires `import` to precede any doc-comment command, so the header above is written as a
-- plain block comment; its text is verbatim as requested.)

import Mathlib

/-!
The main result of this file is `Brockian.PracticalNumbers.PracticalTwinInfinitude`:
there are infinitely many `n` such that both `n` and `n + 2` are practical numbers.

The proof is completely explicit. We show that for every `t`, the pair
`(2 * (3 ^ 2 ^ t - 1), 2 * 3 ^ 2 ^ t)` is a pair of practical numbers differing by `2`
(e.g. `(4, 6)`, `(16, 18)`, `(160, 162)`, `(13120, 13122)`, ...).

The engine is the classical closure property `IsPractical.mul`: if `n` is practical and
`0 < m ≤ σ n + 1`, then `n * m` is practical. Iterating it along the factorisation
`3 ^ 2 ^ t - 1 = 2 * (3 ^ 2 ^ 0 + 1) * (3 ^ 2 ^ 1 + 1) * ⋯ * (3 ^ 2 ^ (t-1) + 1)`
(realised here as a simple induction on `t`) yields practicality of `2 * (3 ^ 2 ^ t - 1)`,
while practicality of `2 * 3 ^ a` is an even simpler induction.
-/

namespace Brockian.PracticalNumbers

open Finset

/-- `n` is a *practical number* if it is positive and every `k ≤ n` can be written as a sum of
distinct divisors of `n`. -/
def IsPractical (n : ℕ) : Prop :=
  0 < n ∧ ∀ k ≤ n, ∃ S ⊆ n.divisors, ∑ d ∈ S, d = k

/-- A finite set of positive integers in which every element is at most one more than the sum of
the smaller elements is *complete*: its subset sums realize every value up to the total sum. -/
theorem exists_subset_sum_of_chain {S : Finset ℕ} (hpos : ∀ x ∈ S, 0 < x)
    (h : ∀ x ∈ S, x ≤ 1 + ∑ y ∈ S.filter (· < x), y) :
    ∀ k ≤ ∑ x ∈ S, x, ∃ T ⊆ S, ∑ x ∈ T, x = k := by
  induction S using Finset.strongInduction with
  | _ S ih =>
    intro k hk
    rcases S.eq_empty_or_nonempty with rfl | hne
    · simp only [Finset.sum_empty, Nat.le_zero] at hk
      exact ⟨∅, by simp [hk]⟩
    · set M := S.max' hne with hMdef
      have hM : M ∈ S := S.max'_mem hne
      set S' := S.erase M with hS'def
      have hsub : S' ⊂ S := Finset.erase_ssubset hM
      have hfil : ∀ x ∈ S', S'.filter (· < x) = S.filter (· < x) := by
        intro x hx
        have hxS : x ∈ S := Finset.mem_of_mem_erase hx
        apply Finset.Subset.antisymm
        · exact Finset.filter_subset_filter _ (Finset.erase_subset _ _)
        · intro y hy
          simp only [Finset.mem_filter] at hy ⊢
          refine ⟨Finset.mem_erase.2 ⟨?_, hy.1⟩, hy.2⟩
          intro hyM
          have : x ≤ M := S.le_max' x hxS
          omega
      have hpos' : ∀ x ∈ S', 0 < x := fun x hx => hpos x (Finset.mem_of_mem_erase hx)
      have h' : ∀ x ∈ S', x ≤ 1 + ∑ y ∈ S'.filter (· < x), y := by
        intro x hx
        rw [hfil x hx]
        exact h x (Finset.mem_of_mem_erase hx)
      have hsum : ∑ x ∈ S', x + M = ∑ x ∈ S, x := Finset.sum_erase_add _ _ hM
      by_cases hk' : k ≤ ∑ x ∈ S', x
      · obtain ⟨T, hT, hTsum⟩ := ih S' hsub hpos' h' k hk'
        exact ⟨T, hT.trans (Finset.erase_subset _ _), hTsum⟩
      · push_neg at hk'
        have hMle : M ≤ 1 + ∑ x ∈ S', x := by
          refine le_trans (h M hM) ?_
          have hsubf : S.filter (· < M) ⊆ S' := by
            intro y hy
            simp only [Finset.mem_filter] at hy
            exact Finset.mem_erase.2 ⟨by omega, hy.1⟩
          exact Nat.add_le_add_left (Finset.sum_le_sum_of_subset hsubf) 1
        have hMk : M ≤ k := by omega
        obtain ⟨T, hT, hTsum⟩ := ih S' hsub hpos' h' (k - M) (by omega)
        refine ⟨insert M T, ?_, ?_⟩
        · intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · exact hM
          · exact (hT.trans (Finset.erase_subset _ _)) hx
        · have hMT : M ∉ T := fun hc => (Finset.mem_erase.1 (hT hc)).1 rfl
          rw [Finset.sum_insert hMT, hTsum]
          omega

/-- For a practical number, each divisor is at most one more than the sum of the smaller
divisors. -/
theorem divisor_le_sum_smaller {n : ℕ} (hn : IsPractical n) {d : ℕ} (hd : d ∈ n.divisors) :
    d ≤ 1 + ∑ e ∈ n.divisors.filter (· < d), e := by
  by_contra hc
  push_neg at hc
  set s := ∑ e ∈ n.divisors.filter (· < d), e with hs
  have hdn : d ≤ n := Nat.le_of_dvd hn.1 (Nat.dvd_of_mem_divisors hd)
  have hle : s + 1 ≤ n := by omega
  obtain ⟨T, hT, hTsum⟩ := hn.2 (s + 1) hle
  have hTlt : ∀ x ∈ T, x < d := by
    intro x hx
    have : x ≤ s + 1 :=
      hTsum ▸ Finset.single_le_sum (f := fun i => i) (fun i _ => Nat.zero_le i) hx
    omega
  have hTsub : T ⊆ n.divisors.filter (· < d) := fun x hx =>
    Finset.mem_filter.2 ⟨hT hx, hTlt x hx⟩
  have h2 : ∑ x ∈ T, x ≤ s := Finset.sum_le_sum_of_subset hTsub
  omega

/-- For a practical number `n`, every `k` up to `σ n` is a sum of distinct divisors of `n`. -/
theorem IsPractical.full {n : ℕ} (hn : IsPractical n) :
    ∀ k ≤ ∑ d ∈ n.divisors, d, ∃ S ⊆ n.divisors, ∑ d ∈ S, d = k :=
  exists_subset_sum_of_chain (fun _ hx => Nat.pos_of_mem_divisors hx)
    (fun _ hx => divisor_le_sum_smaller hn hx)

/-- The basic multiplicative closure property: if `n` is practical and `0 < m ≤ σ n + 1`, then
`n * m` is practical. -/
theorem IsPractical.mul {n m : ℕ} (hn : IsPractical n) (hm : 0 < m)
    (hle : m ≤ 1 + ∑ d ∈ n.divisors, d) : IsPractical (n * m) := by
  have hnm : n * m ≠ 0 := Nat.mul_ne_zero hn.1.ne' hm.ne'
  refine ⟨Nat.pos_of_ne_zero hnm, ?_⟩
  intro k hk
  set q := k / m with hq
  set r := k % m with hrdef
  have hkqr : q * m + r = k := by rw [hq, hrdef, Nat.mul_comm]; exact Nat.div_add_mod k m
  have hrlt : r < m := Nat.mod_lt _ hm
  have hrle : r ≤ ∑ d ∈ n.divisors, d := by omega
  have hqn : q ≤ n := Nat.le_of_mul_le_mul_right (by omega) hm
  obtain ⟨R, hR, hRsum⟩ := hn.full r hrle
  obtain ⟨Q, hQ, hQsum⟩ := hn.2 q hqn
  have hinj : ∀ a ∈ Q, ∀ b ∈ Q, a * m = b * m → a = b :=
    fun a _ b _ hab => Nat.eq_of_mul_eq_mul_right hm hab
  have hdisj : Disjoint R (Q.image (· * m)) := by
    rw [Finset.disjoint_right]
    intro x hx hxR
    simp only [Finset.mem_image] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors (hQ hd)
    have h1 : d * m ≤ r :=
      hRsum ▸ Finset.single_le_sum (f := fun i => i) (fun i _ => Nat.zero_le i) hxR
    have h2 : m ≤ d * m := Nat.le_mul_of_pos_left m hd1
    omega
  refine ⟨R ∪ Q.image (· * m), ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · have hx' := hR hx
      rw [Nat.mem_divisors] at hx' ⊢
      exact ⟨hx'.1.trans (Dvd.intro m rfl), hnm⟩
    · simp only [Finset.mem_image] at hx
      obtain ⟨d, hd, rfl⟩ := hx
      have hx' := hQ hd
      rw [Nat.mem_divisors] at hx' ⊢
      exact ⟨Nat.mul_dvd_mul_right hx'.1 m, hnm⟩
  · rw [Finset.sum_union hdisj, Finset.sum_image hinj, hRsum]
    have hs : ∑ x ∈ Q, x * m = (∑ x ∈ Q, x) * m := by rw [Finset.sum_mul]
    rw [hs, hQsum]
    omega

theorem self_le_sum_divisors {n : ℕ} (hn : 0 < n) : n ≤ ∑ d ∈ n.divisors, d :=
  Finset.single_le_sum (f := fun i => i) (fun i _ => Nat.zero_le i)
    (Nat.mem_divisors_self n hn.ne')

/-- A convenient weakening of `IsPractical.mul`: if `n` is practical and `0 < m ≤ n + 1`, then
`n * m` is practical. -/
theorem IsPractical.mul' {n m : ℕ} (hn : IsPractical n) (hm : 0 < m) (hle : m ≤ n + 1) :
    IsPractical (n * m) :=
  hn.mul hm (by have := self_le_sum_divisors hn.1; omega)

theorem practical_one : IsPractical 1 := by
  refine ⟨one_pos, ?_⟩
  intro k hk
  interval_cases k
  · exact ⟨∅, by simp⟩
  · exact ⟨{1}, by simp⟩

theorem practical_two : IsPractical 2 := by
  simpa using practical_one.mul' (m := 2) (by norm_num) (by norm_num)

/-- `2 * 3 ^ a` is practical. -/
theorem practical_two_mul_three_pow (a : ℕ) : IsPractical (2 * 3 ^ a) := by
  induction a with
  | zero => simpa using practical_two
  | succ a ih =>
      have h3 : (3:ℕ) ≤ 2 * 3 ^ a + 1 := by
        have : (1:ℕ) ≤ 3 ^ a := Nat.one_le_pow _ _ (by norm_num)
        omega
      have hres := ih.mul' (m := 3) (by norm_num) h3
      have he : 2 * 3 ^ a * 3 = 2 * 3 ^ (a + 1) := by ring
      rwa [he] at hres

theorem nat_sq_sub_one (x : ℕ) (hx : 1 ≤ x) : x * x - 1 = (x - 1) * (x + 1) := by
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  have h2 : (y + 1) * (y + 1) = y * (y + 1 + 1) + 1 := by ring
  simp only [Nat.add_sub_cancel]
  omega

/-- `2 * (3 ^ 2 ^ t - 1)` is practical. -/
theorem practical_two_mul_three_pow_two_pow_sub_one (t : ℕ) :
    IsPractical (2 * (3 ^ 2 ^ t - 1)) := by
  induction t with
  | zero =>
      have h : 2 * (3 ^ 2 ^ 0 - 1) = 2 * 2 := by norm_num
      rw [h]
      exact practical_two.mul' (by norm_num) (by norm_num)
  | succ t ih =>
      have hx3 : 3 ≤ 3 ^ 2 ^ t := by
        calc (3:ℕ) = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ 2 ^ t := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow
      have hsq : (3:ℕ) ^ 2 ^ (t + 1) = 3 ^ 2 ^ t * 3 ^ 2 ^ t := by
        rw [← pow_add]
        congr 1
        rw [pow_succ]
        omega
      have hstep : (3:ℕ) ^ 2 ^ (t + 1) - 1 = (3 ^ 2 ^ t - 1) * (3 ^ 2 ^ t + 1) := by
        rw [hsq, nat_sq_sub_one _ (by omega)]
      have hle : 3 ^ 2 ^ t + 1 ≤ 2 * (3 ^ 2 ^ t - 1) + 1 := by omega
      have hres := ih.mul' (m := 3 ^ 2 ^ t + 1) (by omega) hle
      have he : 2 * (3 ^ 2 ^ t - 1) * (3 ^ 2 ^ t + 1) = 2 * (3 ^ 2 ^ (t + 1) - 1) := by
        rw [hstep]; ring
      rwa [he] at hres

/-- Sanity check that the definition is not vacuous: `5` is not practical (it has divisors `1`
and `5`, so `4` is not a sum of distinct divisors). -/
theorem not_practical_five : ¬ IsPractical 5 := by
  rintro ⟨-, h⟩
  obtain ⟨S, hS, hsum⟩ := h 4 (by norm_num)
  have hd : Nat.divisors 5 = {1, 5} := by decide
  rw [hd] at hS
  have hmem : S ∈ ({1, 5} : Finset ℕ).powerset := Finset.mem_powerset.2 hS
  fin_cases hmem <;> simp_all

/-- **Practical twin infinitude**: there are infinitely many `n` such that both `n` and `n + 2`
are practical numbers. -/
theorem PracticalTwinInfinitude :
    ∀ N : ℕ, ∃ n : ℕ, N < n ∧ IsPractical n ∧ IsPractical (n + 2) := by
  intro N
  refine ⟨2 * (3 ^ 2 ^ N - 1), ?_, practical_two_mul_three_pow_two_pow_sub_one N, ?_⟩
  · have h1 : N < 2 ^ N := Nat.lt_two_pow_self
    have h2 : N < 3 ^ N := Nat.lt_pow_self (by norm_num)
    have h3 : (3:ℕ) ^ N ≤ 3 ^ 2 ^ N := Nat.pow_le_pow_right (by norm_num) h1.le
    have h4 : (3:ℕ) ≤ 3 ^ 2 ^ N := by
      calc (3:ℕ) = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ 2 ^ N := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow
    omega
  · have h4 : (1:ℕ) ≤ 3 ^ 2 ^ N := Nat.one_le_pow _ _ (by norm_num)
    have he : 2 * (3 ^ 2 ^ N - 1) + 2 = 2 * 3 ^ 2 ^ N := by omega
    rw [he]
    exact practical_two_mul_three_pow (2 ^ N)

/-- The set of practical numbers `n` with `n + 2` also practical is infinite. -/
theorem setOf_practical_twin_infinite :
    {n : ℕ | IsPractical n ∧ IsPractical (n + 2)}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨N, hN⟩
  obtain ⟨n, hn, h1, h2⟩ := PracticalTwinInfinitude N
  have : n ≤ N := hN (show n ∈ {n : ℕ | IsPractical n ∧ IsPractical (n + 2)} from ⟨h1, h2⟩)
  omega

end Brockian.PracticalNumbers

