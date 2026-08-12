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

import Brockian.EquidistributionBVReduction

/-!
# An equidistributed sequence

This file exhibits a concrete sequence in `[0,1)` satisfying
`Brockian.EquidistributionBVReduction.Equidistributed`, showing that the equidistribution
hypothesis of `configCount_density_of_BV` is satisfiable (so the theorem is not vacuous).

The sequence is the "triangular block" sequence: the `k`-th block lists the `k+1` points
`0/(k+1), 1/(k+1), …, k/(k+1)`.
-/

open Filter Set
open scoped Topology

namespace Brockian.EquidistributionBVReduction

/-- Start index of block `k`; block `k` consists of the `k+1` indices
`blockStart k, …, blockStart k + k`. -/
def blockStart : ℕ → ℕ
  | 0 => 0
  | (k+1) => blockStart k + (k+1)

lemma blockStart_succ (k : ℕ) : blockStart (k+1) = blockStart k + (k+1) := rfl

lemma blockStart_strictMono : StrictMono blockStart := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [blockStart_succ]
  omega

lemma le_blockStart (k : ℕ) : k ≤ blockStart k := by
  induction k with
  | zero => simp [blockStart]
  | succ k ih => rw [blockStart_succ]; omega

lemma two_mul_blockStart (k : ℕ) : 2 * blockStart k = k * (k+1) := by
  induction k with
  | zero => simp [blockStart]
  | succ k ih => rw [blockStart_succ]; ring_nf; ring_nf at ih; omega

/-- The index of the block containing `n`. -/
def blockIdx (n : ℕ) : ℕ := Nat.findGreatest (fun k => blockStart k ≤ n) n

lemma blockStart_blockIdx_le (n : ℕ) : blockStart (blockIdx n) ≤ n :=
  Nat.findGreatest_spec (P := fun k => blockStart k ≤ n) (Nat.zero_le n)
    (show blockStart 0 ≤ n from Nat.zero_le n)

lemma lt_blockStart_blockIdx_succ (n : ℕ) : n < blockStart (blockIdx n + 1) := by
  by_contra h
  push_neg at h
  have h1 : blockIdx n + 1 ≤ n := le_trans (le_blockStart (blockIdx n + 1)) h
  exact Nat.findGreatest_is_greatest (P := fun k => blockStart k ≤ n) (k := blockIdx n + 1)
    (Nat.lt_succ_self _) h1 h

lemma le_blockIdx {k n : ℕ} (h : blockStart k ≤ n) : k ≤ blockIdx n :=
  Nat.le_findGreatest (le_trans (le_blockStart k) h) h

lemma blockIdx_blockStart_add (k i : ℕ) (hi : i < k + 1) : blockIdx (blockStart k + i) = k := by
  have h2 : blockStart k + i < blockStart (k+1) := by rw [blockStart_succ]; omega
  set n := blockStart k + i with hn
  have hle : blockStart (blockIdx n) ≤ n := blockStart_blockIdx_le n
  have hlt : n < blockStart (blockIdx n + 1) := lt_blockStart_blockIdx_succ n
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt' | hgt
  · have : blockStart (blockIdx n + 1) ≤ blockStart k :=
      blockStart_strictMono.monotone (by omega)
    omega
  · have : blockStart (k+1) ≤ blockStart (blockIdx n) :=
      blockStart_strictMono.monotone (by omega)
    omega

/-- The triangular block sequence: the `k`-th block lists `0/(k+1), …, k/(k+1)`. -/
noncomputable def triSeq (n : ℕ) : ℝ :=
  ((n - blockStart (blockIdx n) : ℕ) : ℝ) / (blockIdx n + 1)

lemma triSeq_mem (n : ℕ) : triSeq n ∈ Set.Ico (0:ℝ) 1 := by
  have h1 := blockStart_blockIdx_le n
  have h2 := lt_blockStart_blockIdx_succ n
  rw [blockStart_succ] at h2
  have hnum : n - blockStart (blockIdx n) < blockIdx n + 1 := by omega
  have hpos : (0:ℝ) < (blockIdx n : ℝ) + 1 := by positivity
  refine ⟨by unfold triSeq; positivity, ?_⟩
  unfold triSeq
  rw [div_lt_one hpos]
  exact_mod_cast hnum

lemma triSeq_block (k i : ℕ) (hi : i < k + 1) :
    triSeq (blockStart k + i) = (i : ℝ) / ((k : ℝ) + 1) := by
  unfold triSeq
  rw [blockIdx_blockStart_add k i hi]
  simp

lemma sum_range_blockStart {M : Type*} [AddCommMonoid M] (g : ℕ → M) (K : ℕ) :
    ∑ n ∈ Finset.range (blockStart K), g n
      = ∑ k ∈ Finset.range K, ∑ i ∈ Finset.range (k+1), g (blockStart k + i) := by
  induction K with
  | zero => simp [blockStart]
  | succ K ih =>
      rw [blockStart_succ, Finset.sum_range_add, ih,
        Finset.sum_range_succ (fun k => ∑ i ∈ Finset.range (k+1), g (blockStart k + i)) K]

lemma blockStart_eq_sum (K : ℕ) : blockStart K = ∑ k ∈ Finset.range K, (k+1) := by
  induction K with
  | zero => simp [blockStart]
  | succ K ih => rw [blockStart_succ, Finset.sum_range_succ, ih]

open Classical in
lemma configCount_eq_sum (x : ℕ → ℝ) (s : Set ℝ) (N : ℕ) :
    configCount x s N = ∑ n ∈ Finset.range N, if x n ∈ s then 1 else 0 := by
  unfold configCount
  rw [Finset.card_filter]

open Classical in
lemma block_count_eq (t : ℝ) (ht1 : t ≤ 1) (k : ℕ) :
    (∑ i ∈ Finset.range (k+1), if ((i:ℝ)/((k:ℝ)+1)) ∈ Set.Ico (0:ℝ) t then 1 else 0)
      = ⌈t * ((k:ℝ)+1)⌉₊ := by
  have hpos : (0:ℝ) < (k:ℝ) + 1 := by positivity
  have hceil_le : ⌈t * ((k:ℝ)+1)⌉₊ ≤ k + 1 := by
    rw [Nat.ceil_le]
    push_cast
    nlinarith
  have hset : (Finset.range (k+1)).filter (fun i : ℕ => ((i:ℝ)/((k:ℝ)+1)) ∈ Set.Ico (0:ℝ) t)
      = Finset.range ⌈t * ((k:ℝ)+1)⌉₊ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Set.mem_Ico]
    constructor
    · rintro ⟨hi, h0, hlt⟩
      rw [div_lt_iff₀ hpos] at hlt
      exact Nat.lt_ceil.2 (by linarith)
    · intro hi
      have h1 : (i:ℝ) < t * ((k:ℝ)+1) := Nat.lt_ceil.1 hi
      refine ⟨by omega, by positivity, ?_⟩
      rw [div_lt_iff₀ hpos]
      linarith
  rw [← Finset.card_filter, hset, Finset.card_range]

open Classical in
/-- The count over a full prefix of blocks. -/
lemma configCount_blockStart (t : ℝ) (ht1 : t ≤ 1) (K : ℕ) :
    configCount triSeq (Set.Ico 0 t) (blockStart K)
      = ∑ k ∈ Finset.range K, ⌈t * ((k:ℝ)+1)⌉₊ := by
  rw [configCount_eq_sum, sum_range_blockStart]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← block_count_eq t ht1 k]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [triSeq_block k i (Finset.mem_range.1 hi)]
  congr 1

/-- Two-sided bound for the count over a full prefix of blocks. -/
lemma configCount_blockStart_bounds (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (K : ℕ) :
    t * blockStart K ≤ (configCount triSeq (Set.Ico 0 t) (blockStart K) : ℝ) ∧
      (configCount triSeq (Set.Ico 0 t) (blockStart K) : ℝ) ≤ t * blockStart K + K := by
  have hsum : ((blockStart K : ℕ) : ℝ) = ∑ k ∈ Finset.range K, ((k:ℝ)+1) := by
    rw [blockStart_eq_sum]
    push_cast
    ring_nf
  rw [configCount_blockStart t ht1 K]
  push_cast
  constructor
  · rw [hsum, Finset.mul_sum]
    exact Finset.sum_le_sum (fun k _ => Nat.le_ceil _)
  · have hb : ∀ k ∈ Finset.range K,
        ((⌈t * ((k:ℝ)+1)⌉₊ : ℝ)) ≤ t * ((k:ℝ)+1) + 1 := by
      intro k _
      have h0 : (0:ℝ) ≤ t * ((k:ℝ)+1) := by positivity
      exact le_of_lt (Nat.ceil_lt_add_one h0)
    calc (∑ k ∈ Finset.range K, (⌈t * ((k:ℝ)+1)⌉₊ : ℝ))
        ≤ ∑ k ∈ Finset.range K, (t * ((k:ℝ)+1) + 1) := Finset.sum_le_sum hb
      _ = t * blockStart K + K := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hsum]
          simp

open Classical in
/-- Monotonicity and a crude upper bound for counts along the sequence. -/
lemma configCount_mono_bounds (x : ℕ → ℝ) (s : Set ℝ) {b N : ℕ} (hbN : b ≤ N) :
    configCount x s b ≤ configCount x s N ∧
      configCount x s N ≤ configCount x s b + (N - b) := by
  have hN : N = b + (N - b) := by omega
  rw [configCount_eq_sum, configCount_eq_sum, hN, Finset.sum_range_add]
  constructor
  · omega
  · have : ∑ i ∈ Finset.range (N - b), (if x (b + i) ∈ s then 1 else 0) ≤ N - b := by
      calc ∑ i ∈ Finset.range (N - b), (if x (b + i) ∈ s then 1 else 0)
          ≤ ∑ _i ∈ Finset.range (N - b), 1 := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            split <;> omega
        _ = N - b := by simp
    omega

lemma tendsto_blockIdx : Tendsto blockIdx atTop atTop := by
  refine tendsto_atTop_atTop.2 (fun M => ⟨blockStart M, fun N hN => le_blockIdx hN⟩)

/-- The triangular block sequence is equidistributed. -/
theorem equidistributed_triSeq : Equidistributed triSeq := by
  intro t ht
  obtain ⟨ht0, ht1⟩ := ht
  have hkey : ∀ᶠ N : ℕ in atTop,
      ‖(configCount triSeq (Set.Ico 0 t) N : ℝ) / N - t‖ ≤ 4 / (blockIdx N : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with N hN1
    set K := blockIdx N with hK
    have hb := blockStart_blockIdx_le N
    have hlt := lt_blockStart_blockIdx_succ N
    rw [blockStart_succ] at hlt
    rw [← hK] at hb hlt
    have hK1 : 1 ≤ K := le_blockIdx (k := 1) (by simpa [blockStart] using hN1)
    have hmono := configCount_mono_bounds triSeq (Set.Ico 0 t) hb
    obtain ⟨hlow, hupp⟩ := configCount_blockStart_bounds t ht0 ht1 K
    have hNb : N - blockStart K ≤ K := by omega
    have hN0 : (0:ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN1
    have hKR : (0:ℝ) < K := by exact_mod_cast hK1
    have hbR : (blockStart K : ℝ) ≤ N := by exact_mod_cast hb
    have hNbR : (N : ℝ) - blockStart K ≤ K := by
      have : ((N - blockStart K : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast hNb
      rwa [Nat.cast_sub hb] at this
    have hC1 : (configCount triSeq (Set.Ico 0 t) (blockStart K) : ℝ)
        ≤ (configCount triSeq (Set.Ico 0 t) N : ℝ) := by exact_mod_cast hmono.1
    have hC2 : (configCount triSeq (Set.Ico 0 t) N : ℝ)
        ≤ (configCount triSeq (Set.Ico 0 t) (blockStart K) : ℝ) + ((N : ℝ) - blockStart K) := by
      have := hmono.2
      have hcast : ((configCount triSeq (Set.Ico 0 t) (blockStart K) + (N - blockStart K) : ℕ) : ℝ)
          = (configCount triSeq (Set.Ico 0 t) (blockStart K) : ℝ) + ((N : ℝ) - blockStart K) := by
        rw [Nat.cast_add, Nat.cast_sub hb]
      calc (configCount triSeq (Set.Ico 0 t) N : ℝ)
          ≤ ((configCount triSeq (Set.Ico 0 t) (blockStart K) + (N - blockStart K) : ℕ) : ℝ) := by
            exact_mod_cast this
        _ = _ := hcast
    -- two-sided estimate
    have habs : |(configCount triSeq (Set.Ico 0 t) N : ℝ) - t * N| ≤ 2 * K := by
      rw [abs_le]
      constructor
      · nlinarith
      · nlinarith
    have hsq : (K:ℝ) * K ≤ 2 * N := by
      have h2 : 2 * blockStart K = K * (K+1) := two_mul_blockStart K
      have : ((K:ℝ)) * ((K:ℝ)+1) = 2 * (blockStart K : ℝ) := by exact_mod_cast h2.symm
      nlinarith
    have heq : (configCount triSeq (Set.Ico 0 t) N : ℝ) / N - t
        = ((configCount triSeq (Set.Ico 0 t) N : ℝ) - t * N) / N := by
      field_simp
    rw [heq, norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hN0]
    rw [div_le_div_iff₀ hN0 hKR]
    nlinarith [abs_nonneg ((configCount triSeq (Set.Ico 0 t) N : ℝ) - t * N)]
  have hzero : Tendsto (fun N : ℕ => 4 / (blockIdx N : ℝ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => (blockIdx N : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp tendsto_blockIdx
    exact h1.const_div_atTop 4
  have := squeeze_zero_norm' hkey hzero
  have h2 := this.add_const t
  simpa using h2

/-- Unconditional instance of the main theorem for the concrete sequence `triSeq`. -/
theorem configCount_density_of_BV_triSeq (f : ℝ → ℝ) (hf : BoundedVariationOn f (Set.Icc 0 1)) :
    Tendsto (fun N => (∑ n ∈ Finset.range N, f (triSeq n)) / N) atTop
      (𝓝 (∫ t in (0:ℝ)..1, f t)) :=
  configCount_density_of_BV triSeq triSeq_mem equidistributed_triSeq f hf

/-- The equidistribution hypothesis of `configCount_density_of_BV` is satisfiable. -/
theorem exists_equidistributed :
    ∃ x : ℕ → ℝ, (∀ n, x n ∈ Set.Ico (0:ℝ) 1) ∧ Equidistributed x :=
  ⟨triSeq, triSeq_mem, equidistributed_triSeq⟩

end Brockian.EquidistributionBVReduction

import Mathlib

/-!
# Config Count Density Of BV
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_density_of_BV
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Filter Set
open scoped Topology

namespace Brockian.EquidistributionBVReduction

open Classical in
/-- `configCount x s N` is the number of indices `n < N` for which the point `x n`
lies in the "configuration set" `s`. -/
noncomputable def configCount (x : ℕ → ℝ) (s : Set ℝ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => x n ∈ s)).card

/-- The sequence `x` is equidistributed in `[0,1)`: for every `t ∈ [0,1]` the density of
indices `n` with `x n ∈ [0,t)` is `t`. -/
def Equidistributed (x : ℕ → ℝ) : Prop :=
  ∀ t ∈ Set.Icc (0:ℝ) 1,
    Tendsto (fun N => (configCount x (Set.Ico 0 t) N : ℝ) / N) atTop (𝓝 t)

/-- Counting over `[0,b)` splits as counting over `[0,a)` plus counting over `[a,b)`. -/
lemma configCount_split (x : ℕ → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (N : ℕ) :
    configCount x (Set.Ico 0 b) N
      = configCount x (Set.Ico 0 a) N + configCount x (Set.Ico a b) N := by
  classical
  unfold configCount
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext n
    simp only [Finset.mem_union, Finset.mem_filter, Set.mem_Ico]
    constructor
    · rintro ⟨hn, h0, hb⟩
      rcases lt_or_ge (x n) a with h | h
      · exact Or.inl ⟨hn, h0, h⟩
      · exact Or.inr ⟨hn, h, hb⟩
    · rintro (⟨hn, h0, h⟩ | ⟨hn, h, hb⟩)
      · exact ⟨hn, h0, lt_of_lt_of_le h hab⟩
      · exact ⟨hn, le_trans ha h, hb⟩
  · rw [Finset.disjoint_left]
    intro n hn hn'
    simp only [Finset.mem_filter, Set.mem_Ico] at hn hn'
    linarith [hn.2.2, hn'.2.1]

/-- Densities of half-open subintervals of `[0,1]` are their lengths. -/
lemma tendsto_configCount_Ico (x : ℕ → ℝ) (hequi : Equidistributed x) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (fun N => (configCount x (Set.Ico a b) N : ℝ) / N) atTop (𝓝 (b - a)) := by
  have h1 := hequi b ⟨le_trans ha hab, hb⟩
  have h2 := hequi a ⟨ha, le_trans hab hb⟩
  refine (h1.sub h2).congr (fun N => ?_)
  rw [configCount_split x ha hab N]
  push_cast
  ring

/-- The configuration count of `[i/m, (i+1)/m)` counts the fibre `⌊m * x n⌋₊ = i`. -/
lemma configCount_eq_fiber_card (x : ℕ → ℝ) (hx : ∀ n, x n ∈ Set.Ico (0:ℝ) 1) {m : ℕ}
    (hm : 0 < m) (N i : ℕ) :
    configCount x (Set.Ico ((i : ℝ) / m) (((i : ℝ) + 1) / m)) N
      = ((Finset.range N).filter (fun n => ⌊(m : ℝ) * x n⌋₊ = i)).card := by
  classical
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  unfold configCount
  congr 1
  ext n
  simp only [Finset.mem_filter, Set.mem_Ico, and_congr_right_iff]
  intro _
  have h0 : (0:ℝ) ≤ (m:ℝ) * x n := mul_nonneg (le_of_lt hm') (hx n).1
  rw [Nat.floor_eq_iff h0, div_le_iff₀ hm', lt_div_iff₀ hm', mul_comm (x n) (m:ℝ)]

/-- Splitting a sum over `n < N` according to the fibres of `n ↦ ⌊m * x n⌋₊`. -/
lemma sum_fiberwise_aux (x : ℕ → ℝ) (hx : ∀ n, x n ∈ Set.Ico (0:ℝ) 1) (g : ℕ → ℝ) {m : ℕ}
    (hm : 0 < m) (N : ℕ) :
    ∑ n ∈ Finset.range N, g n
      = ∑ i ∈ Finset.range m,
          ∑ n ∈ (Finset.range N).filter (fun n => ⌊(m:ℝ) * x n⌋₊ = i), g n := by
  classical
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  refine (Finset.sum_fiberwise_of_maps_to ?_ _).symm
  intro n _
  simp only [Finset.mem_range]
  rw [Nat.floor_lt (mul_nonneg hm'.le (hx n).1)]
  calc (m:ℝ) * x n < (m:ℝ) * 1 := by nlinarith [(hx n).2]
    _ = m := by ring

/-- Lower Riemann-type bound on the sum of `f (x n)`. -/
lemma lower_sum_le_sum (x : ℕ → ℝ) (hx : ∀ n, x n ∈ Set.Ico (0:ℝ) 1) (f : ℝ → ℝ)
    (hf : MonotoneOn f (Set.Icc 0 1)) {m : ℕ} (hm : 0 < m) (N : ℕ) :
    ∑ i ∈ Finset.range m,
        f ((i : ℝ) / m) * (configCount x (Set.Ico ((i : ℝ) / m) (((i : ℝ) + 1) / m)) N : ℝ)
      ≤ ∑ n ∈ Finset.range N, f (x n) := by
  classical
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  rw [sum_fiberwise_aux x hx (fun n => f (x n)) hm N]
  refine Finset.sum_le_sum ?_
  intro i hi
  have hi' : i < m := Finset.mem_range.1 hi
  have hmem : ((i:ℝ)/m) ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by positivity, by rw [div_le_one hm']; exact_mod_cast hi'.le⟩
  rw [configCount_eq_fiber_card x hx hm N i]
  have hle : ∀ n ∈ (Finset.range N).filter (fun n => ⌊(m:ℝ) * x n⌋₊ = i),
      f ((i:ℝ)/m) ≤ f (x n) := by
    intro n hn
    have hfl : ⌊(m:ℝ) * x n⌋₊ = i := (Finset.mem_filter.1 hn).2
    have h0 : (0:ℝ) ≤ (m:ℝ) * x n := mul_nonneg hm'.le (hx n).1
    have hile : ((i:ℝ)) ≤ (m:ℝ) * x n := by
      have h := Nat.floor_le h0
      rw [hfl] at h
      exact h
    refine hf hmem ⟨(hx n).1, (hx n).2.le⟩ ?_
    rw [div_le_iff₀ hm']
    nlinarith
  have hcard := Finset.card_nsmul_le_sum
    ((Finset.range N).filter (fun n => ⌊(m:ℝ) * x n⌋₊ = i)) (fun n => f (x n))
    (f ((i:ℝ)/m)) hle
  simpa [nsmul_eq_mul, mul_comm] using hcard

/-- Upper Riemann-type bound on the sum of `f (x n)`. -/
lemma sum_le_upper_sum (x : ℕ → ℝ) (hx : ∀ n, x n ∈ Set.Ico (0:ℝ) 1) (f : ℝ → ℝ)
    (hf : MonotoneOn f (Set.Icc 0 1)) {m : ℕ} (hm : 0 < m) (N : ℕ) :
    ∑ n ∈ Finset.range N, f (x n)
      ≤ ∑ i ∈ Finset.range m,
          f (((i : ℝ) + 1) / m) *
            (configCount x (Set.Ico ((i : ℝ) / m) (((i : ℝ) + 1) / m)) N : ℝ) := by
  classical
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  rw [sum_fiberwise_aux x hx (fun n => f (x n)) hm N]
  refine Finset.sum_le_sum ?_
  intro i hi
  have hi' : i < m := Finset.mem_range.1 hi
  have hmem : (((i:ℝ)+1)/m) ∈ Set.Icc (0:ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hm']
    exact_mod_cast hi'
  rw [configCount_eq_fiber_card x hx hm N i]
  have hle : ∀ n ∈ (Finset.range N).filter (fun n => ⌊(m:ℝ) * x n⌋₊ = i),
      f (x n) ≤ f (((i:ℝ)+1)/m) := by
    intro n hn
    have hfl : ⌊(m:ℝ) * x n⌋₊ = i := (Finset.mem_filter.1 hn).2
    have hlt : (m:ℝ) * x n < (i:ℝ) + 1 := by
      have h := Nat.lt_floor_add_one ((m:ℝ) * x n)
      rw [hfl] at h
      exact_mod_cast h
    refine hf ⟨(hx n).1, (hx n).2.le⟩ hmem ?_
    rw [le_div_iff₀ hm']
    nlinarith
  have hcard := Finset.sum_le_card_nsmul
    ((Finset.range N).filter (fun n => ⌊(m:ℝ) * x n⌋₊ = i)) (fun n => f (x n))
    (f (((i:ℝ)+1)/m)) hle
  simpa [nsmul_eq_mul, mul_comm] using hcard

/-- Averages of step sums converge to the corresponding Riemann sum. -/
lemma tendsto_step_average (x : ℕ → ℝ) (hequi : Equidistributed x) (c : ℕ → ℝ) {m : ℕ}
    (hm : 0 < m) :
    Tendsto (fun N => (∑ i ∈ Finset.range m,
        c i * (configCount x (Set.Ico ((i : ℝ) / m) (((i : ℝ) + 1) / m)) N : ℝ)) / N)
      atTop (𝓝 (∑ i ∈ Finset.range m, c i / m)) := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hterm : ∀ i ∈ Finset.range m,
      Tendsto (fun N =>
          c i * ((configCount x (Set.Ico ((i : ℝ) / m) (((i : ℝ) + 1) / m)) N : ℝ) / N))
        atTop (𝓝 (c i / m)) := by
    intro i hi
    have hi' : i < m := Finset.mem_range.1 hi
    have hi1 : (i:ℝ) + 1 ≤ m := by exact_mod_cast hi'
    have h := tendsto_configCount_Ico x hequi (a := (i:ℝ)/m) (b := ((i:ℝ)+1)/m)
      (by positivity) (by gcongr; linarith) (by rw [div_le_one hm']; exact hi1)
    have hlen : ((i:ℝ)+1)/m - (i:ℝ)/m = 1/m := by field_simp; ring
    rw [hlen] at h
    have h2 := h.const_mul (c i)
    simpa [mul_one_div] using h2
  have hsum := tendsto_finset_sum (Finset.range m) hterm
  refine hsum.congr (fun N => ?_)
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl (fun i _ => by rw [mul_div_assoc])

/-- Bounds for the integral of a monotone function over one subinterval of the partition. -/
lemma integral_subinterval_bounds (f : ℝ → ℝ) (hf : MonotoneOn f (Set.Icc 0 1)) {m i : ℕ}
    (hm : 0 < m) (hi : i < m) :
    f ((i:ℝ)/m)/m ≤ (∫ t in ((i:ℝ)/m)..(((i:ℝ)+1)/m), f t) ∧
    (∫ t in ((i:ℝ)/m)..(((i:ℝ)+1)/m), f t) ≤ f (((i:ℝ)+1)/m)/m := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hi1 : (i:ℝ) + 1 ≤ m := by exact_mod_cast hi
  have hab : (i:ℝ)/m ≤ ((i:ℝ)+1)/m := by gcongr; linarith
  have hsub : Set.Icc ((i:ℝ)/m) (((i:ℝ)+1)/m) ⊆ Set.Icc (0:ℝ) 1 := by
    intro t ht
    refine ⟨le_trans (by positivity) ht.1, le_trans ht.2 ?_⟩
    rw [div_le_one hm']; exact hi1
  have hmono : MonotoneOn f (Set.uIcc ((i:ℝ)/m) (((i:ℝ)+1)/m)) := by
    rw [Set.uIcc_of_le hab]; exact hf.mono hsub
  have hint : IntervalIntegrable f MeasureTheory.volume ((i:ℝ)/m) (((i:ℝ)+1)/m) :=
    hmono.intervalIntegrable
  have hlen : ((i:ℝ)+1)/m - (i:ℝ)/m = 1/m := by field_simp; ring
  constructor
  · have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
      (f := fun _ => f ((i:ℝ)/m)) (g := f) hab intervalIntegrable_const hint
      (fun t ht => hf (hsub ⟨le_refl _, hab⟩) (hsub ht) ht.1)
    rw [intervalIntegral.integral_const, smul_eq_mul, hlen] at h
    have heq : f ((i:ℝ)/m)/m = 1/(m:ℝ) * f ((i:ℝ)/m) := by ring
    rw [heq]; exact h
  · have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) (f := f)
      (g := fun _ => f (((i:ℝ)+1)/m)) hab hint intervalIntegrable_const
      (fun t ht => hf (hsub ht) (hsub ⟨hab, le_refl _⟩) ht.2)
    rw [intervalIntegral.integral_const, smul_eq_mul, hlen] at h
    have heq : f (((i:ℝ)+1)/m)/m = 1/(m:ℝ) * f (((i:ℝ)+1)/m) := by ring
    rw [heq]; exact h

/-- The integral over `[0,1]` splits along the uniform partition into `m` pieces. -/
lemma integral_eq_sum_subintervals (f : ℝ → ℝ) (hf : MonotoneOn f (Set.Icc 0 1)) {m : ℕ}
    (hm : 0 < m) :
    (∫ t in (0:ℝ)..1, f t)
      = ∑ i ∈ Finset.range m, ∫ t in ((i:ℝ)/m)..(((i:ℝ)+1)/m), f t := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hint : ∀ k < m,
      IntervalIntegrable f MeasureTheory.volume ((k:ℝ)/m) ((((k:ℕ)+1 : ℕ):ℝ)/m) := by
    intro k hk
    have hi1 : (k:ℝ) + 1 ≤ m := by exact_mod_cast hk
    have hab : (k:ℝ)/m ≤ ((k:ℝ)+1)/m := by gcongr; linarith
    have hsub : Set.Icc ((k:ℝ)/m) (((k:ℝ)+1)/m) ⊆ Set.Icc (0:ℝ) 1 := by
      intro t ht
      refine ⟨le_trans (by positivity) ht.1, le_trans ht.2 ?_⟩
      rw [div_le_one hm']; exact hi1
    have hmo : MonotoneOn f (Set.uIcc ((k:ℝ)/m) (((k:ℝ)+1)/m)) := by
      rw [Set.uIcc_of_le hab]; exact hf.mono hsub
    have h2 := hmo.intervalIntegrable (μ := MeasureTheory.volume)
    push_cast
    exact h2
  have h := intervalIntegral.sum_integral_adjacent_intervals (μ := MeasureTheory.volume)
    (f := f) (a := fun k : ℕ => (k:ℝ)/m) (n := m) hint
  simp only [Nat.cast_zero, zero_div, Nat.cast_add, Nat.cast_one, div_self (ne_of_gt hm')] at h
  exact h.symm

/-- The lower Riemann sum underestimates the integral. -/
lemma lower_riemann_le_integral (f : ℝ → ℝ) (hf : MonotoneOn f (Set.Icc 0 1)) {m : ℕ}
    (hm : 0 < m) :
    ∑ i ∈ Finset.range m, f ((i : ℝ) / m) / m ≤ ∫ t in (0:ℝ)..1, f t := by
  rw [integral_eq_sum_subintervals f hf hm]
  exact Finset.sum_le_sum
    (fun i hi => (integral_subinterval_bounds f hf hm (Finset.mem_range.1 hi)).1)

/-- The upper Riemann sum overestimates the integral. -/
lemma integral_le_upper_riemann (f : ℝ → ℝ) (hf : MonotoneOn f (Set.Icc 0 1)) {m : ℕ}
    (hm : 0 < m) :
    (∫ t in (0:ℝ)..1, f t) ≤ ∑ i ∈ Finset.range m, f (((i : ℝ) + 1) / m) / m := by
  rw [integral_eq_sum_subintervals f hf hm]
  exact Finset.sum_le_sum
    (fun i hi => (integral_subinterval_bounds f hf hm (Finset.mem_range.1 hi)).2)

/-- The gap between the upper and lower Riemann sums is `(f 1 - f 0) / m`. -/
lemma upper_sub_lower_riemann (f : ℝ → ℝ) {m : ℕ} (hm : 0 < m) :
    (∑ i ∈ Finset.range m, f (((i : ℝ) + 1) / m) / m)
      - ∑ i ∈ Finset.range m, f ((i : ℝ) / m) / m = (f 1 - f 0) / m := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have htel := Finset.sum_range_sub (f := fun i : ℕ => f ((i:ℝ)/m)/m) m
  rw [← Finset.sum_sub_distrib]
  have hcongr : ∀ i ∈ Finset.range m,
      f (((i : ℝ) + 1) / m) / m - f ((i : ℝ) / m) / m
        = (fun i : ℕ => f ((i:ℝ)/m)/m) (i+1) - (fun i : ℕ => f ((i:ℝ)/m)/m) i := by
    intro i _
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl hcongr, htel]
  simp [div_self (ne_of_gt hm')]
  ring

/-- Equidistribution implies convergence of Birkhoff-type averages for monotone weights. -/
theorem configCount_density_of_monotoneOn (x : ℕ → ℝ) (hx : ∀ n, x n ∈ Set.Ico (0:ℝ) 1)
    (hequi : Equidistributed x) (f : ℝ → ℝ) (hf : MonotoneOn f (Set.Icc 0 1)) :
    Tendsto (fun N => (∑ n ∈ Finset.range N, f (x n)) / N) atTop (𝓝 (∫ t in (0:ℝ)..1, f t)) := by
  set I : ℝ := ∫ t in (0:ℝ)..1, f t with hI
  have hf01 : f 0 ≤ f 1 :=
    hf ⟨le_refl 0, zero_le_one⟩ ⟨zero_le_one, le_refl 1⟩ zero_le_one
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    have hIa : 0 < I - a := sub_pos.2 ha
    obtain ⟨m, hm⟩ := exists_nat_gt ((f 1 - f 0)/(I - a))
    have hm0 : (0:ℝ) < m := lt_of_le_of_lt (div_nonneg (by linarith) hIa.le) hm
    have hmpos : 0 < m := by exact_mod_cast hm0
    have hgap : (f 1 - f 0)/m < I - a := by
      have h := (div_lt_iff₀ hIa).1 hm
      rw [div_lt_iff₀ hm0]
      nlinarith
    have hL : a < ∑ i ∈ Finset.range m, f ((i:ℝ)/m)/m := by
      have h1 := lower_riemann_le_integral f hf hmpos
      have h2 := integral_le_upper_riemann f hf hmpos
      have h3 := upper_sub_lower_riemann f hmpos
      linarith
    have htend := tendsto_step_average x hequi (fun i => f ((i:ℝ)/m)) hmpos
    filter_upwards [(tendsto_order.1 htend).1 a hL] with N hN
    have hlow := lower_sum_le_sum x hx f hf hmpos N
    calc a < (∑ i ∈ Finset.range m,
          f ((i:ℝ)/m) * (configCount x (Set.Ico ((i : ℝ) / m) (((i : ℝ) + 1) / m)) N : ℝ)) / N :=
          hN
      _ ≤ (∑ n ∈ Finset.range N, f (x n)) / N := by gcongr
  · intro b hb
    have hIb : 0 < b - I := sub_pos.2 hb
    obtain ⟨m, hm⟩ := exists_nat_gt ((f 1 - f 0)/(b - I))
    have hm0 : (0:ℝ) < m := lt_of_le_of_lt (div_nonneg (by linarith) hIb.le) hm
    have hmpos : 0 < m := by exact_mod_cast hm0
    have hgap : (f 1 - f 0)/m < b - I := by
      have h := (div_lt_iff₀ hIb).1 hm
      rw [div_lt_iff₀ hm0]
      nlinarith
    have hU : ∑ i ∈ Finset.range m, f (((i:ℝ)+1)/m)/m < b := by
      have h1 := lower_riemann_le_integral f hf hmpos
      have h2 := integral_le_upper_riemann f hf hmpos
      have h3 := upper_sub_lower_riemann f hmpos
      linarith
    have htend := tendsto_step_average x hequi (fun i => f (((i:ℝ)+1)/m)) hmpos
    filter_upwards [(tendsto_order.1 htend).2 b hU] with N hN
    have hup := sum_le_upper_sum x hx f hf hmpos N
    calc (∑ n ∈ Finset.range N, f (x n)) / N
        ≤ (∑ i ∈ Finset.range m,
            f (((i:ℝ)+1)/m) *
              (configCount x (Set.Ico ((i : ℝ) / m) (((i : ℝ) + 1) / m)) N : ℝ)) / N := by gcongr
      _ < b := hN

/-- **Equidistribution ⟹ BV densities.** If a sequence `x` in `[0,1)` is equidistributed
(i.e. the configuration counts of all initial intervals `[0,t)` have density `t`), then for
every function `f` of bounded variation on `[0,1]` the averages `(1/N) ∑_{n < N} f (x n)`
converge to `∫₀¹ f`. This discharges the bounded-variation hypothesis of the reduction. -/
theorem configCount_density_of_BV (x : ℕ → ℝ) (hx : ∀ n, x n ∈ Set.Ico (0:ℝ) 1)
    (hequi : Equidistributed x) (f : ℝ → ℝ) (hf : BoundedVariationOn f (Set.Icc 0 1)) :
    Tendsto (fun N => (∑ n ∈ Finset.range N, f (x n)) / N) atTop (𝓝 (∫ t in (0:ℝ)..1, f t)) := by
  obtain ⟨p, q, hp, hq, rfl⟩ :=
    hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  have hpint : IntervalIntegrable p MeasureTheory.volume 0 1 := by
    refine MonotoneOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le (zero_le_one : (0:ℝ) ≤ 1)]
    exact hp
  have hqint : IntervalIntegrable q MeasureTheory.volume 0 1 := by
    refine MonotoneOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le (zero_le_one : (0:ℝ) ≤ 1)]
    exact hq
  have hintsub : (∫ t in (0:ℝ)..1, (p - q) t)
      = (∫ t in (0:ℝ)..1, p t) - ∫ t in (0:ℝ)..1, q t := by
    simpa [Pi.sub_apply] using intervalIntegral.integral_sub hpint hqint
  rw [hintsub]
  have hpt := configCount_density_of_monotoneOn x hx hequi p hp
  have hqt := configCount_density_of_monotoneOn x hx hequi q hq
  refine (hpt.sub hqt).congr (fun N => ?_)
  rw [← sub_div, ← Finset.sum_sub_distrib]
  simp [Pi.sub_apply]

end Brockian.EquidistributionBVReduction

