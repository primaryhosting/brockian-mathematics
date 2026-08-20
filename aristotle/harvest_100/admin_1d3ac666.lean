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
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Finset

namespace Brockian.Equidistribution

/-- Triangular numbers: `T m = 1 + 2 + ⋯ + m = m (m+1) / 2`. -/
def T (m : ℕ) : ℕ := ∑ i ∈ Finset.range m, (i + 1)

lemma T_succ (m : ℕ) : T (m + 1) = T m + (m + 1) := Finset.sum_range_succ _ _

lemma T_mono : Monotone T := by
  intro m n h
  unfold T
  gcongr

lemma two_mul_T (m : ℕ) : 2 * T m = m * (m + 1) := by
  induction m with
  | zero => simp [T]
  | succ n ih => rw [T_succ]; nlinarith [ih]

lemma self_lt_T_succ (n : ℕ) : n < T (n + 1) := by
  have := T_succ n
  omega

lemma blk_exists (n : ℕ) : ∃ m : ℕ, n < T (m + 1) := ⟨n, self_lt_T_succ n⟩

/-- `blk n` is the index of the block containing `n`, i.e. the unique `m` with
`T m ≤ n < T (m+1)`. -/
noncomputable def blk (n : ℕ) : ℕ := Nat.find (blk_exists n)

lemma lt_T_blk_succ (n : ℕ) : n < T (blk n + 1) := Nat.find_spec (blk_exists n)

lemma T_blk_le (n : ℕ) : T (blk n) ≤ n := by
  rcases Nat.eq_zero_or_pos (blk n) with h | h
  · simp [h, T]
  · obtain ⟨m, hm⟩ : ∃ m, blk n = m + 1 := ⟨blk n - 1, by omega⟩
    have hmin : ¬ (n < T (m + 1)) :=
      Nat.find_min (blk_exists n) (show m < blk n by omega)
    rw [hm]
    omega

lemma blk_eq (m n : ℕ) (h1 : T m ≤ n) (h2 : n < T (m + 1)) : blk n = m := by
  have hle : blk n ≤ m := Nat.find_le h2
  by_contra hne
  have hlt : blk n < m := lt_of_le_of_ne hle hne
  have h3 : T (blk n + 1) ≤ T m := T_mono (by omega)
  have h4 := lt_T_blk_succ n
  omega

/-- The equidistributed sequence: block `m` consists of the `m+1` points
`0/(m+1), 1/(m+1), …, m/(m+1)`. -/
noncomputable def u (n : ℕ) : ℝ := ((n - T (blk n) : ℕ) : ℝ) / (blk n + 1)

lemma u_block (m k : ℕ) (hk : k ≤ m) : u (T m + k) = (k : ℝ) / (m + 1) := by
  have hb : blk (T m + k) = m := by
    refine blk_eq m _ (by omega) ?_
    rw [T_succ]; omega
  simp [u, hb]

lemma u_nonneg (n : ℕ) : 0 ≤ u n := by
  apply div_nonneg (Nat.cast_nonneg _)
  positivity

lemma u_lt_one (n : ℕ) : u n < 1 := by
  have h1 : (n - T (blk n) : ℕ) < blk n + 1 := by
    have h2 := lt_T_blk_succ n
    have h3 := T_blk_le n
    have h4 := T_succ (blk n)
    omega
  have hpos : (0:ℝ) < (blk n : ℝ) + 1 := by positivity
  rw [u, div_lt_one hpos]
  exact_mod_cast h1

/-- The counting function: how many of `u 0, …, u (N-1)` lie in `[a, b)`. -/
noncomputable def Cnt (a b : ℝ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => u n ∈ Set.Ico a b)).card

lemma Cnt_add (a b : ℝ) (p q : ℕ) :
    Cnt a b (p + q) =
      Cnt a b p + ((Finset.range q).filter (fun k => u (p + k) ∈ Set.Ico a b)).card := by
  classical
  rw [Cnt, Cnt, Finset.range_add, Finset.filter_union, Finset.card_union_of_disjoint,
    Finset.filter_map, Finset.card_map]
  · rfl
  · apply Finset.disjoint_filter_filter
    simp only [Finset.disjoint_left, Finset.mem_range, Finset.mem_map]
    rintro x hx ⟨y, hy, rfl⟩
    simp only [addLeftEmbedding_apply] at hx ⊢
    omega

/-- The number of points of `{0/L, 1/L, …, (L-1)/L}` in `[a,b)` differs from `(b-a) L`
by at most one. -/
lemma arith_block_card (L : ℕ) (hL : 0 < L) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    |((((Finset.range L).filter (fun k : ℕ => ((k : ℝ) / L) ∈ Set.Ico a b)).card : ℝ)) -
      (b - a) * L| ≤ 1 := by
  have hLR : (0:ℝ) < (L:ℝ) := by exact_mod_cast hL
  have hset : ((Finset.range L).filter (fun k : ℕ => ((k : ℝ) / L) ∈ Set.Ico a b))
      = Finset.Ico ⌈a * L⌉₊ ⌈b * L⌉₊ := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Set.mem_Ico, Finset.mem_Ico,
      Nat.ceil_le, Nat.lt_ceil]
    constructor
    · rintro ⟨hk, h1, h2⟩
      refine ⟨?_, ?_⟩
      · rw [le_div_iff₀ hLR] at h1; linarith
      · rw [div_lt_iff₀ hLR] at h2; linarith
    · rintro ⟨h1, h2⟩
      have hkL : (k:ℝ) < L := by nlinarith
      refine ⟨by exact_mod_cast hkL, ?_, ?_⟩
      · rw [le_div_iff₀ hLR]; linarith
      · rw [div_lt_iff₀ hLR]; linarith
  rw [hset, Nat.card_Ico]
  have hx : (0:ℝ) ≤ a * L := by positivity
  have hy : (0:ℝ) ≤ b * L := by nlinarith
  have hle : ⌈a * L⌉₊ ≤ ⌈b * L⌉₊ := Nat.ceil_le_ceil (by nlinarith)
  rw [Nat.cast_sub hle]
  have h1 := Nat.le_ceil (a * L)
  have h2 := Nat.le_ceil (b * L)
  have h3 := Nat.ceil_lt_add_one hx
  have h4 := Nat.ceil_lt_add_one hy
  rw [abs_le]
  constructor <;> nlinarith

lemma block_card (m : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    |((((Finset.range (m + 1)).filter (fun k => u (T m + k) ∈ Set.Ico a b)).card : ℝ)) -
      (b - a) * ((m : ℝ) + 1)| ≤ 1 := by
  have hrw : ((Finset.range (m + 1)).filter (fun k => u (T m + k) ∈ Set.Ico a b)) =
      ((Finset.range (m + 1)).filter (fun k : ℕ => ((k : ℝ) / ((m : ℝ) + 1)) ∈ Set.Ico a b)) := by
    apply Finset.filter_congr
    intro k hk
    rw [u_block m k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
  rw [hrw]
  have h := arith_block_card (m + 1) (Nat.succ_pos m) a b ha hab hb
  push_cast at h
  exact h

lemma Cnt_T (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (M : ℕ) :
    |(Cnt a b (T M) : ℝ) - (b - a) * T M| ≤ M := by
  induction M with
  | zero => simp [Cnt, T]
  | succ n ih =>
      have hstep := block_card n a b ha hab hb
      have hT : T (n + 1) = T n + (n + 1) := T_succ n
      have hc := Cnt_add a b (T n) (n + 1)
      rw [hT, hc]
      push_cast [hT]
      have hsplit : ((Cnt a b (T n) : ℝ) +
            (((Finset.range (n + 1)).filter (fun k => u (T n + k) ∈ Set.Ico a b)).card : ℝ)) -
          (b - a) * ((T n : ℝ) + ((n : ℝ) + 1)) =
          ((Cnt a b (T n) : ℝ) - (b - a) * (T n : ℝ)) +
          ((((Finset.range (n + 1)).filter (fun k => u (T n + k) ∈ Set.Ico a b)).card : ℝ) -
            (b - a) * ((n : ℝ) + 1)) := by ring
      rw [hsplit]
      calc |((Cnt a b (T n) : ℝ) - (b - a) * (T n : ℝ)) +
              ((((Finset.range (n + 1)).filter (fun k => u (T n + k) ∈ Set.Ico a b)).card : ℝ) -
                (b - a) * ((n : ℝ) + 1))|
          ≤ |(Cnt a b (T n) : ℝ) - (b - a) * (T n : ℝ)| +
              |(((Finset.range (n + 1)).filter (fun k => u (T n + k) ∈ Set.Ico a b)).card : ℝ) -
                (b - a) * ((n : ℝ) + 1)| := abs_add_le _ _
        _ ≤ (n : ℝ) + 1 := by linarith

lemma Cnt_le_add (a b : ℝ) (p q : ℕ) : Cnt a b (p + q) ≤ Cnt a b p + q := by
  rw [Cnt_add]
  have h : ((Finset.range q).filter (fun k => u (p + k) ∈ Set.Ico a b)).card ≤ q := by
    simpa using Finset.card_filter_le (Finset.range q) _
  omega

lemma Cnt_mono_add (a b : ℝ) (p q : ℕ) : Cnt a b p ≤ Cnt a b (p + q) := by
  rw [Cnt_add]; omega

/-- Main quantitative estimate: the empirical proportion in `[a,b)` differs from `b - a`
by at most `6 / (blk N + 1)`. -/
lemma abs_Cnt_div_sub_le (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (N : ℕ)
    (hN : 1 ≤ blk N) :
    |(Cnt a b N : ℝ) / N - (b - a)| ≤ 6 / ((blk N : ℝ) + 1) := by
  set M := blk N with hMdef
  have hTM : T M ≤ N := T_blk_le N
  have hNlt : N < T (M + 1) := lt_T_blk_succ N
  have hTsucc : T (M + 1) = T M + (M + 1) := T_succ M
  obtain ⟨r, hr⟩ : ∃ r, N = T M + r := ⟨N - T M, by omega⟩
  have hrM : r ≤ M := by omega
  have hCT := Cnt_T a b ha hab hb M
  have hup : Cnt a b N ≤ Cnt a b (T M) + r := by rw [hr]; exact Cnt_le_add a b (T M) r
  have hlow : Cnt a b (T M) ≤ Cnt a b N := by rw [hr]; exact Cnt_mono_add a b (T M) r
  have hT1 : T 1 ≤ T M := T_mono hN
  have hTMpos : 0 < T M := by
    have : T 1 = 1 := by simp [T]
    omega
  have hNpos : (0:ℝ) < (N : ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hupR : (Cnt a b N : ℝ) ≤ (Cnt a b (T M) : ℝ) + (r : ℝ) := by exact_mod_cast hup
  have hlowR : (Cnt a b (T M) : ℝ) ≤ (Cnt a b N : ℝ) := by exact_mod_cast hlow
  have hNR : (N : ℝ) = (T M : ℝ) + (r : ℝ) := by exact_mod_cast hr
  have h2TR : 2 * (T M : ℝ) = (M : ℝ) * ((M : ℝ) + 1) := by
    have := two_mul_T M
    exact_mod_cast this
  have hrMR : (r : ℝ) ≤ (M : ℝ) := by exact_mod_cast hrM
  have hr0 : (0:ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
  have hba0 : (0:ℝ) ≤ b - a := by linarith
  have hba1 : b - a ≤ 1 := by linarith
  have hCTabs := abs_le.mp hCT
  have hkey : |(Cnt a b N : ℝ) - (b - a) * (N : ℝ)| ≤ 3 * (M : ℝ) := by
    rw [abs_le]
    constructor <;> nlinarith [hCTabs.1, hCTabs.2]
  have hM1pos : (0:ℝ) < (M : ℝ) + 1 := by positivity
  have hsplit : (Cnt a b N : ℝ) / (N : ℝ) - (b - a)
      = ((Cnt a b N : ℝ) - (b - a) * (N : ℝ)) / (N : ℝ) := by
    field_simp
  rw [hsplit, abs_div, abs_of_pos hNpos, div_le_div_iff₀ hNpos hM1pos]
  have hTMR : (T M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hTM
  nlinarith [hkey, hM1pos, hTMR, h2TR]

theorem tendsto_blk_atTop : Tendsto blk atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro M
  refine ⟨T M, fun n hn => ?_⟩
  by_contra h
  have h1 : T (blk n + 1) ≤ T M := T_mono (by omega)
  have h2 := lt_T_blk_succ n
  omega

/-- **Existence of an equidistributed sequence.**  There is a sequence in `[0,1)` such that for
every subinterval `[a,b) ⊆ [0,1]` the asymptotic proportion of terms landing in `[a,b)` exists
and equals its length `b - a`. -/
theorem equidistribution_of_asymptotic_exists :
    ∃ u : ℕ → ℝ, (∀ n, u n ∈ Set.Ico (0 : ℝ) 1) ∧
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
        Tendsto
          (fun N : ℕ =>
            (((Finset.range N).filter (fun n => u n ∈ Set.Ico a b)).card : ℝ) / N)
          atTop (nhds (b - a)) := by
  refine ⟨u, fun n => ⟨u_nonneg n, u_lt_one n⟩, ?_⟩
  intro a b ha hab hb
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M, hM⟩ := exists_nat_gt (6 / ε)
  refine ⟨T (M + 1), fun N hN => ?_⟩
  have hblk : M + 1 ≤ blk N := by
    by_contra h
    have h1 : T (blk N + 1) ≤ T (M + 1) := T_mono (by omega)
    have h2 := lt_T_blk_succ N
    omega
  have h1 : |(Cnt a b N : ℝ) / N - (b - a)| ≤ 6 / ((blk N : ℝ) + 1) :=
    abs_Cnt_div_sub_le a b ha hab hb N (by omega)
  have hMpos : (0:ℝ) < (M : ℝ) + 1 := by positivity
  have h2 : (6 : ℝ) / ((blk N : ℝ) + 1) ≤ 6 / ((M : ℝ) + 1) := by
    apply div_le_div_of_nonneg_left (by norm_num) hMpos
    have hcast : (M : ℝ) ≤ (blk N : ℝ) := by exact_mod_cast (by omega : M ≤ blk N)
    linarith
  have h3 : (6 : ℝ) / ((M : ℝ) + 1) < ε := by
    rw [div_lt_iff₀ hMpos]
    have h6 : 6 / ε < (M : ℝ) := hM
    rw [div_lt_iff₀ hε] at h6
    nlinarith
  rw [Real.dist_eq]
  calc |(((Finset.range N).filter (fun n => u n ∈ Set.Ico a b)).card : ℝ) / N - (b - a)|
      = |(Cnt a b N : ℝ) / N - (b - a)| := rfl
    _ ≤ 6 / ((blk N : ℝ) + 1) := h1
    _ ≤ 6 / ((M : ℝ) + 1) := h2
    _ < ε := h3

end Brockian.Equidistribution

