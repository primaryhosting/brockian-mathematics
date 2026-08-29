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

This file constructs an explicit sequence in `[0, 1)` whose empirical distribution is
asymptotically the uniform one: for every subinterval `[a, b) ⊆ [0, 1)` the proportion of
the first `N` terms lying in `[a, b)` converges to `b - a`.

The construction is the "triangular block" sequence
`0/1 ; 0/2, 1/2 ; 0/3, 1/3, 2/3 ; 0/4, …` .
-/

open Filter Topology

namespace Brockian.Equidistribution

/-- Triangular numbers: `tri k = 0 + 1 + ⋯ + k`. -/
def tri : ℕ → ℕ
  | 0 => 0
  | (k + 1) => tri k + (k + 1)

@[simp] lemma tri_zero : tri 0 = 0 := rfl

lemma tri_succ (k : ℕ) : tri (k + 1) = tri k + (k + 1) := rfl

lemma tri_lt_tri_succ (k : ℕ) : tri k < tri (k + 1) := by
  rw [tri_succ]; omega

lemma tri_strictMono : StrictMono tri := strictMono_nat_of_lt_succ tri_lt_tri_succ

lemma le_tri (k : ℕ) : k ≤ tri k := by
  cases k with
  | zero => simp
  | succ k => rw [tri_succ]; omega

lemma two_mul_tri (k : ℕ) : 2 * tri k = k * (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih => rw [tri_succ]; nlinarith [ih]

/-- The block index of `n`: the largest `k` with `tri k ≤ n`. -/
def idx (n : ℕ) : ℕ := Nat.findGreatest (fun k => tri k ≤ n) n

lemma tri_idx_le (n : ℕ) : tri (idx n) ≤ n := by
  have := Nat.findGreatest_spec (P := fun k => tri k ≤ n) (m := 0) (Nat.zero_le n)
    (by simp)
  exact this

lemma lt_tri_idx_succ (n : ℕ) : n < tri (idx n + 1) := by
  by_cases h : idx n + 1 ≤ n
  · have h' : ¬ (tri (idx n + 1) ≤ n) :=
      Nat.findGreatest_is_greatest (P := fun k => tri k ≤ n) (Nat.lt_succ_self (idx n)) h
    omega
  · have := le_tri (idx n + 1)
    omega

lemma idx_eq_of_mem_block {k n : ℕ} (h1 : tri k ≤ n) (h2 : n < tri (k + 1)) : idx n = k := by
  have hle : k ≤ idx n := Nat.le_findGreatest (le_trans (le_tri k) h1) h1
  have hlt : idx n < k + 1 := by
    by_contra hc
    have hmono : tri (k + 1) ≤ tri (idx n) := tri_strictMono.monotone (by omega)
    have := tri_idx_le n
    omega
  omega

/-- The triangular-block sequence: the `n`-th term is `(n - tri (idx n)) / (idx n + 1)`. -/
noncomputable def seq (n : ℕ) : ℝ := ((n - tri (idx n) : ℕ) : ℝ) / ((idx n : ℝ) + 1)

lemma seq_mem_Ico (n : ℕ) : seq n ∈ Set.Ico (0 : ℝ) 1 := by
  have h1 : tri (idx n) ≤ n := tri_idx_le n
  have h2 : n < tri (idx n) + (idx n + 1) := by
    have := lt_tri_idx_succ n; rw [tri_succ] at this; omega
  have hpos : (0 : ℝ) < (idx n : ℝ) + 1 := by positivity
  constructor
  · exact div_nonneg (by positivity) (le_of_lt hpos)
  · rw [seq, div_lt_one hpos]
    have hlt : (n - tri (idx n) : ℕ) < idx n + 1 := by omega
    exact_mod_cast hlt

lemma seq_eq_of_mem_block {k n : ℕ} (h1 : tri k ≤ n) (h2 : n < tri (k + 1)) :
    seq n = ((n - tri k : ℕ) : ℝ) / ((k : ℝ) + 1) := by
  rw [seq, idx_eq_of_mem_block h1 h2]

/-- Equidistribution of a sequence in `[0,1)`: the proportion of the first `N` terms falling in
`[a, b)` tends to `b - a`. -/
def IsEquidistributed (u : ℕ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
    Tendsto (fun N : ℕ =>
        (((Finset.range N).filter (fun n => u n ∈ Set.Ico a b)).card : ℝ) / (N : ℝ))
      atTop (𝓝 (b - a))

section Counting

variable (a b : ℝ)

/-- Number of the first `N` terms of `seq` lying in `[a, b)`. -/
noncomputable def cnt (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => seq n ∈ Set.Ico a b)).card

/-- The number of `j < m` with `j / m ∈ [a, b)`. -/
noncomputable def blockCnt (m : ℕ) : ℕ :=
  ((Finset.range m).filter (fun j : ℕ => ((j : ℝ) / (m : ℝ)) ∈ Set.Ico a b)).card

lemma blockCnt_eq (m : ℕ) (hm : 0 < m) (hb : b ≤ 1) :
    blockCnt a b m = ⌈b * m⌉₊ - ⌈a * m⌉₊ := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hceil_le : ⌈b * m⌉₊ ≤ m := by
    have hbm : b * m ≤ (m : ℝ) := by nlinarith
    exact Nat.ceil_le.2 (by exact_mod_cast hbm)
  have hset : ((Finset.range m).filter (fun j : ℕ => ((j : ℝ) / (m : ℝ)) ∈ Set.Ico a b))
      = Finset.Ico ⌈a * m⌉₊ ⌈b * m⌉₊ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, Set.mem_Ico]
    constructor
    · rintro ⟨hj, hja, hjb⟩
      refine ⟨Nat.ceil_le.2 ?_, Nat.lt_ceil.2 ?_⟩
      · rw [le_div_iff₀ hmR] at hja; linarith
      · rw [div_lt_iff₀ hmR] at hjb; linarith
    · rintro ⟨hja, hjb⟩
      have hja' : a * m ≤ (j : ℝ) := by
        have hc : ((⌈a * m⌉₊ : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast hja
        linarith [Nat.le_ceil (a * m)]
      have hjb' : (j : ℝ) < b * m := Nat.lt_ceil.1 hjb
      refine ⟨by omega, ?_, ?_⟩
      · rw [le_div_iff₀ hmR]; linarith
      · rw [div_lt_iff₀ hmR]; linarith
  rw [blockCnt, hset, Nat.card_Ico]

lemma blockCnt_bound (m : ℕ) (hm : 0 < m) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    |((blockCnt a b m : ℕ) : ℝ) - (m : ℝ) * (b - a)| ≤ 1 := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hA0 : (0 : ℝ) ≤ a * m := by positivity
  have hB0 : (0 : ℝ) ≤ b * m := by nlinarith
  have hA1 : a * m ≤ (⌈a * m⌉₊ : ℝ) := Nat.le_ceil _
  have hA2 : (⌈a * m⌉₊ : ℝ) < a * m + 1 := Nat.ceil_lt_add_one hA0
  have hB1 : b * m ≤ (⌈b * m⌉₊ : ℝ) := Nat.le_ceil _
  have hB2 : (⌈b * m⌉₊ : ℝ) < b * m + 1 := Nat.ceil_lt_add_one hB0
  have hAB : ⌈a * m⌉₊ ≤ ⌈b * m⌉₊ := Nat.ceil_le_ceil (by nlinarith)
  rw [blockCnt_eq a b m hm hb]
  have hcast : ((⌈b * m⌉₊ - ⌈a * m⌉₊ : ℕ) : ℝ) = (⌈b * m⌉₊ : ℝ) - (⌈a * m⌉₊ : ℝ) :=
    Nat.cast_sub hAB
  rw [hcast, abs_le]
  constructor <;> nlinarith

lemma cnt_succ_block (k : ℕ) :
    cnt a b (tri (k + 1)) = cnt a b (tri k) + blockCnt a b (k + 1) := by
  have hsplit : Finset.range (tri (k + 1))
      = Finset.range (tri k) ∪ Finset.Ico (tri k) (tri (k + 1)) := by
    rw [Finset.range_eq_Ico,
      Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) (le_of_lt (tri_lt_tri_succ k))]
  have hdisj : Disjoint ((Finset.range (tri k)).filter (fun n => seq n ∈ Set.Ico a b))
      ((Finset.Ico (tri k) (tri (k + 1))).filter (fun n => seq n ∈ Set.Ico a b)) := by
    apply Finset.disjoint_filter_filter
    rw [Finset.range_eq_Ico]
    exact Finset.Ico_disjoint_Ico_consecutive 0 (tri k) (tri (k + 1))
  have hcard : ((Finset.Ico (tri k) (tri (k + 1))).filter
      (fun n => seq n ∈ Set.Ico a b)).card = blockCnt a b (k + 1) := by
    rw [blockCnt]
    apply Finset.card_bij' (fun n _ => n - tri k) (fun j _ => j + tri k)
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Ico] at hn
      obtain ⟨⟨h1, h2⟩, h3⟩ := hn
      simp only [Finset.mem_filter, Finset.mem_range]
      have hlt : n - tri k < k + 1 := by rw [tri_succ] at h2; omega
      refine ⟨hlt, ?_⟩
      rw [seq_eq_of_mem_block h1 h2] at h3
      simpa using h3
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj
      obtain ⟨hj1, hj2⟩ := hj
      have h1 : tri k ≤ j + tri k := Nat.le_add_left _ _
      have h2 : j + tri k < tri (k + 1) := by rw [tri_succ]; omega
      simp only [Finset.mem_filter, Finset.mem_Ico]
      refine ⟨⟨h1, h2⟩, ?_⟩
      rw [seq_eq_of_mem_block h1 h2]
      have hjj : j + tri k - tri k = j := by omega
      rw [hjj]
      simpa using hj2
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Ico] at hn
      omega
    · intro j _
      omega
  rw [cnt, cnt, hsplit, Finset.filter_union, Finset.card_union_of_disjoint hdisj, hcard]

lemma cnt_tri_bound (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (K : ℕ) :
    |((cnt a b (tri K) : ℕ) : ℝ) - (tri K : ℝ) * (b - a)| ≤ (K : ℝ) := by
  induction K with
  | zero => simp [cnt]
  | succ K ih =>
      have hbd := blockCnt_bound a b (K + 1) (Nat.succ_pos K) ha hab hb
      rw [cnt_succ_block, tri_succ]
      rw [abs_le] at *
      push_cast at ih hbd ⊢
      constructor <;> [linarith [ih.1, hbd.1]; linarith [ih.2, hbd.2]]

lemma cnt_mono : Monotone (cnt a b) := by
  intro M N hMN
  have hsub : Finset.range M ⊆ Finset.range N := Finset.range_subset_range.mpr hMN
  exact Finset.card_le_card (Finset.filter_subset_filter _ hsub)

/-- Main quantitative estimate: the counting error over `[0, N)` is `O(K)` where `K` is the
block index of `N`. -/
lemma cnt_bound (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (N K : ℕ)
    (h1 : tri K ≤ N) (h2 : N ≤ tri (K + 1)) :
    |((cnt a b N : ℕ) : ℝ) - (N : ℝ) * (b - a)| ≤ 3 * (K : ℝ) + 3 := by
  have hlow : cnt a b (tri K) ≤ cnt a b N := cnt_mono a b h1
  have hhigh : cnt a b N ≤ cnt a b (tri (K + 1)) := cnt_mono a b h2
  have hstep : cnt a b (tri (K + 1)) = cnt a b (tri K) + blockCnt a b (K + 1) :=
    cnt_succ_block a b K
  have hba0 : 0 ≤ b - a := by linarith
  have hba1 : b - a ≤ 1 := by linarith
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have hblock : (blockCnt a b (K + 1) : ℝ) ≤ (K : ℝ) + 2 := by
    have hbb := blockCnt_bound a b (K + 1) (Nat.succ_pos K) ha hab hb
    rw [abs_le] at hbb
    have h := hbb.2
    push_cast at h
    nlinarith
  have htri : (tri K : ℝ) ≤ (N : ℝ) := by exact_mod_cast h1
  have htri2 : (N : ℝ) ≤ (tri K : ℝ) + ((K : ℝ) + 1) := by
    have hn : N ≤ tri K + (K + 1) := by rw [tri_succ] at h2; omega
    exact_mod_cast hn
  have hIH := cnt_tri_bound a b ha hab hb K
  rw [abs_le] at hIH ⊢
  have hlowR : ((cnt a b (tri K) : ℕ) : ℝ) ≤ ((cnt a b N : ℕ) : ℝ) := by exact_mod_cast hlow
  have hhighR : ((cnt a b N : ℕ) : ℝ)
      ≤ ((cnt a b (tri K) : ℕ) : ℝ) + (blockCnt a b (K + 1) : ℝ) := by
    have hle : cnt a b N ≤ cnt a b (tri K) + blockCnt a b (K + 1) := by omega
    exact_mod_cast hle
  constructor <;> nlinarith [hIH.1, hIH.2]

end Counting

lemma exists_block_index (N : ℕ) :
    ∃ K : ℕ, tri K ≤ N ∧ N ≤ tri (K + 1) ∧ (K : ℝ) ≤ Real.sqrt (2 * N) := by
  refine ⟨idx N, tri_idx_le N, le_of_lt (lt_tri_idx_succ N), ?_⟩
  have h : idx N * idx N ≤ 2 * N := by
    have h1 : tri (idx N) ≤ N := tri_idx_le N
    have h2 : 2 * tri (idx N) = idx N * (idx N + 1) := two_mul_tri _
    nlinarith
  have hR : ((idx N : ℝ)) * (idx N : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast h
  have hs : Real.sqrt ((idx N : ℝ) * (idx N : ℝ)) ≤ Real.sqrt (2 * N) := Real.sqrt_le_sqrt hR
  rwa [Real.sqrt_mul_self (Nat.cast_nonneg (idx N))] at hs

/-- The error bound function. -/
noncomputable def errBound (N : ℕ) : ℝ := (3 * Real.sqrt (2 * N) + 3) / (N : ℝ)

lemma errBound_tendsto : Tendsto errBound atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => (3 * Real.sqrt 2 + 3) / Real.sqrt (N : ℝ)) atTop (𝓝 0) := by
    have hs : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    simpa [div_eq_mul_inv, mul_comm] using hs.inv_tendsto_atTop.const_mul (3 * Real.sqrt 2 + 3)
  refine squeeze_zero' (Eventually.of_forall ?_) ?_ h1
  · intro N
    unfold errBound
    positivity
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
    have hsq : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNpos
    have hsqle : Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
      nlinarith [Real.sq_sqrt (le_of_lt hNpos), Real.sqrt_nonneg (N : ℝ),
        Real.one_le_sqrt.2 hN1]
    have hmul : Real.sqrt (2 * N) = Real.sqrt 2 * Real.sqrt (N : ℝ) := by
      rw [← Real.sqrt_mul (by norm_num)]
    unfold errBound
    rw [hmul, div_le_div_iff₀ hNpos hsq]
    have hs2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    nlinarith [Real.sq_sqrt (le_of_lt hNpos), Real.sqrt_nonneg (N : ℝ)]

lemma seq_isEquidistributed : IsEquidistributed seq := by
  intro a b ha hab hb
  have key : ∀ N : ℕ, 1 ≤ N →
      |((cnt a b N : ℕ) : ℝ) / (N : ℝ) - (b - a)| ≤ errBound N := by
    intro N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    obtain ⟨K, h1, h2, h3⟩ := exists_block_index N
    have hbd := cnt_bound a b ha hab hb N K h1 h2
    have hnum : |((cnt a b N : ℕ) : ℝ) - (N : ℝ) * (b - a)| ≤ 3 * Real.sqrt (2 * N) + 3 := by
      refine hbd.trans ?_
      linarith
    have heq : ((cnt a b N : ℕ) : ℝ) / (N : ℝ) - (b - a)
        = (((cnt a b N : ℕ) : ℝ) - (N : ℝ) * (b - a)) / (N : ℝ) := by
      field_simp
    rw [heq, abs_div, abs_of_pos hNpos]
    unfold errBound
    gcongr
  have hz : Tendsto (fun N : ℕ => ((cnt a b N : ℕ) : ℝ) / (N : ℝ) - (b - a)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ errBound_tendsto
    filter_upwards [eventually_ge_atTop 1] with N hN
    simpa [Real.norm_eq_abs] using key N hN
  have hfin := hz.add_const (b - a)
  simpa [cnt] using hfin

/-- **Main theorem.** There exists an equidistributed sequence in `[0, 1)`: the asymptotic
uniform distribution of empirical counts is realised by an explicit sequence, with no
hypotheses assumed. -/
theorem equidistribution_of_asymptotic_exists :
    ∃ u : ℕ → ℝ, (∀ n, u n ∈ Set.Ico (0 : ℝ) 1) ∧ IsEquidistributed u :=
  ⟨seq, seq_mem_Ico, seq_isEquidistributed⟩

end Brockian.Equidistribution

