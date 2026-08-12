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
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

namespace Brockian.Equidistribution

/-- A sequence `u : ℕ → ℝ` is *asymptotically equidistributed mod 1* if for every
subinterval `[a, b) ⊆ [0, 1]` the asymptotic density of the set of indices `n` with
`Int.fract (u n) ∈ [a, b)` exists and equals the length `b - a` of the interval. -/
def AsymptoticallyEquidistributedMod1 (u : ℕ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
    Filter.Tendsto
      (fun N : ℕ =>
        (((Finset.range N).filter fun n => Int.fract (u n) ∈ Set.Ico a b).card : ℝ) / N)
      Filter.atTop (nhds (b - a))

/-! ### An explicit equidistributed sequence

We concatenate the blocks `0/(k+1), 1/(k+1), …, k/(k+1)` for `k = 0, 1, 2, …`. -/

/-- The triangular numbers `tri k = 0 + 1 + ⋯ + k`, the starting index of block `k`. -/
def tri : ℕ → ℕ
  | 0 => 0
  | (k + 1) => tri k + (k + 1)

lemma tri_succ (k : ℕ) : tri (k + 1) = tri k + (k + 1) := rfl

lemma tri_mono : Monotone tri := by
  intro a b hab
  induction b with
  | zero => simp_all
  | succ n ih =>
      rcases Nat.lt_or_ge a (n + 1) with h | h
      · exact le_trans (ih (Nat.lt_succ_iff.mp h)) (by simp [tri_succ])
      · have : a = n + 1 := le_antisymm hab h
        simp [this]

lemma le_tri (k : ℕ) : k ≤ tri k := by
  induction k with
  | zero => simp [tri]
  | succ n ih => rw [tri_succ]; omega

lemma two_mul_tri (k : ℕ) : 2 * tri k = k * (k + 1) := by
  induction k with
  | zero => simp [tri]
  | succ n ih => rw [tri_succ]; ring_nf; ring_nf at ih; omega

lemma exists_blk (n : ℕ) : ∃ k, n < tri (k + 1) :=
  ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) (le_tri (n + 1))⟩

/-- The index of the block containing position `n`. -/
noncomputable def blk (n : ℕ) : ℕ := Nat.find (exists_blk n)

lemma blk_spec (n : ℕ) : tri (blk n) ≤ n ∧ n < tri (blk n + 1) := by
  refine ⟨?_, Nat.find_spec (exists_blk n)⟩
  rcases Nat.eq_zero_or_pos (blk n) with h | h
  · simp [h, tri]
  · have hlt : blk n - 1 < Nat.find (exists_blk n) := by
      have : blk n = Nat.find (exists_blk n) := rfl
      omega
    have hmin := Nat.find_min (exists_blk n) hlt
    have h2 : blk n - 1 + 1 = blk n := by omega
    rw [h2] at hmin
    omega

lemma blk_eq (k m : ℕ) (hm : m ≤ k) : blk (tri k + m) = k := by
  have h1 : tri k + m < tri (k + 1) := by rw [tri_succ]; omega
  have h2 : ∀ j, j < k → ¬ (tri k + m < tri (j + 1)) := by
    intro j hj hcon
    have : tri (j + 1) ≤ tri k := tri_mono (by omega)
    omega
  exact (Nat.find_eq_iff _).mpr ⟨h1, fun j hj => h2 j hj⟩

/-- The equidistributed sequence. -/
noncomputable def useq (n : ℕ) : ℝ := ((n - tri (blk n) : ℕ) : ℝ) / (blk n + 1)

lemma useq_block (k m : ℕ) (hm : m ≤ k) : useq (tri k + m) = (m : ℝ) / (k + 1) := by
  have hb := blk_eq k m hm
  simp [useq, hb]

lemma useq_mem (n : ℕ) : useq n ∈ Set.Ico (0 : ℝ) 1 := by
  obtain ⟨h1, h2⟩ := blk_spec n
  have hm : n - tri (blk n) ≤ blk n := by rw [tri_succ] at h2; omega
  have hpos : (0 : ℝ) < (blk n : ℝ) + 1 := by positivity
  rw [Set.mem_Ico, useq]
  constructor
  · exact div_nonneg (by positivity) (le_of_lt hpos)
  · rw [div_lt_one hpos]
    have : ((n - tri (blk n) : ℕ) : ℝ) ≤ (blk n : ℝ) := by exact_mod_cast hm
    linarith

/-- The counting function: the number of `n < N` with `useq n < x`. -/
noncomputable def cnt (x : ℝ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun n => useq n < x).card

lemma cnt_succ (x : ℝ) (N : ℕ) :
    cnt x (N + 1) = cnt x N + if useq N < x then 1 else 0 := by
  unfold cnt
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : useq N < x <;> simp [h, Finset.card_insert_of_notMem]

lemma lt_iff_lt_ceil (x : ℝ) (K m : ℕ) :
    ((m : ℝ) / ((K : ℝ) + 1) < x) ↔ m < ⌈((K : ℝ) + 1) * x⌉₊ := by
  have h : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  rw [Nat.lt_ceil, div_lt_iff₀ h]
  constructor <;> intro h2 <;> nlinarith [h2]

lemma cnt_block_add (x : ℝ) (K : ℕ) :
    ∀ m ≤ K + 1, cnt x (tri K + m) = cnt x (tri K) + min m ⌈((K : ℝ) + 1) * x⌉₊ := by
  intro m hm
  induction m with
  | zero => simp
  | succ p ih =>
      have hp : p ≤ K := by omega
      have ihp := ih (by omega)
      have hstep : cnt x (tri K + (p + 1))
          = cnt x (tri K + p) + if useq (tri K + p) < x then 1 else 0 := by
        have hrw : tri K + (p + 1) = (tri K + p) + 1 := by omega
        rw [hrw, cnt_succ]
      rw [hstep, ihp, useq_block K p hp]
      by_cases h : (p : ℝ) / ((K : ℝ) + 1) < x
      · have hlt : p < ⌈((K : ℝ) + 1) * x⌉₊ := (lt_iff_lt_ceil x K p).mp h
        simp only [h, if_true]
        omega
      · have hlt : ¬ (p < ⌈((K : ℝ) + 1) * x⌉₊) := fun hc =>
          h ((lt_iff_lt_ceil x K p).mpr hc)
        simp only [h, if_false]
        omega

lemma cnt_tri (x : ℝ) (hx1 : x ≤ 1) (K : ℕ) :
    cnt x (tri K) = ∑ k ∈ Finset.range K, ⌈((k : ℝ) + 1) * x⌉₊ := by
  induction K with
  | zero => simp [tri, cnt]
  | succ K ih =>
      have hceil : ⌈((K : ℝ) + 1) * x⌉₊ ≤ K + 1 := by
        rw [Nat.ceil_le]
        push_cast
        nlinarith
      rw [tri_succ, cnt_block_add x K (K + 1) le_rfl, ih, Finset.sum_range_succ]
      omega

lemma tri_cast (K : ℕ) : (tri K : ℝ) = ∑ k ∈ Finset.range K, ((k : ℝ) + 1) := by
  induction K with
  | zero => simp [tri]
  | succ K ih =>
      rw [tri_succ, Finset.sum_range_succ, ← ih]
      push_cast
      ring

lemma ceil_sub_le_one (y : ℝ) (hy : 0 ≤ y) : |(⌈y⌉₊ : ℝ) - y| ≤ 1 := by
  have h1 : y ≤ (⌈y⌉₊ : ℝ) := Nat.le_ceil y
  have h2 : (⌈y⌉₊ : ℝ) < y + 1 := Nat.ceil_lt_add_one hy
  rw [abs_le]
  constructor <;> linarith

lemma cnt_tri_error (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (K : ℕ) :
    |(cnt x (tri K) : ℝ) - x * tri K| ≤ K := by
  rw [cnt_tri x hx1 K, tri_cast K]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc |∑ k ∈ Finset.range K, ((⌈((k : ℝ) + 1) * x⌉₊ : ℝ) - x * ((k : ℝ) + 1))|
      ≤ ∑ k ∈ Finset.range K, |(⌈((k : ℝ) + 1) * x⌉₊ : ℝ) - x * ((k : ℝ) + 1)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range K, (1 : ℝ) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have hnn : (0 : ℝ) ≤ ((k : ℝ) + 1) * x := by positivity
        have h := ceil_sub_le_one (((k : ℝ) + 1) * x) hnn
        rw [show x * ((k : ℝ) + 1) = ((k : ℝ) + 1) * x by ring]
        exact h
    _ = K := by simp

lemma cnt_error (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (N : ℕ) :
    |(cnt x N : ℝ) - x * N| ≤ 2 * blk N := by
  obtain ⟨h1, h2⟩ := blk_spec N
  set K := blk N with hK
  set m := N - tri K with hm
  have hmK : m ≤ K := by rw [tri_succ] at h2; omega
  have hNsplit : N = tri K + m := by omega
  have hcnt : cnt x N = cnt x (tri K) + min m ⌈((K : ℝ) + 1) * x⌉₊ := by
    rw [hNsplit]; exact cnt_block_add x K m (by omega)
  have hNcast : (N : ℝ) = (tri K : ℝ) + (m : ℝ) := by
    rw [hNsplit]; push_cast; ring
  have hmain := cnt_tri_error x hx0 hx1 K
  have hmin1 : (min m ⌈((K : ℝ) + 1) * x⌉₊ : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast Nat.cast_le.mpr (min_le_left _ _)
  have hmin0 : (0 : ℝ) ≤ (min m ⌈((K : ℝ) + 1) * x⌉₊ : ℝ) := by positivity
  have hmk : (m : ℝ) ≤ (K : ℝ) := by exact_mod_cast hmK
  have hxm0 : (0 : ℝ) ≤ x * m := by positivity
  have hxm1 : x * (m : ℝ) ≤ (K : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have habs : |(min m ⌈((K : ℝ) + 1) * x⌉₊ : ℝ) - x * m| ≤ (K : ℝ) := by
    rw [abs_le]; constructor <;> linarith
  have hsplit : (cnt x N : ℝ) - x * N
      = ((cnt x (tri K) : ℝ) - x * tri K)
        + ((min m ⌈((K : ℝ) + 1) * x⌉₊ : ℝ) - x * m) := by
    rw [hcnt, hNcast]; push_cast; ring
  calc |(cnt x N : ℝ) - x * N|
      ≤ |((cnt x (tri K) : ℝ) - x * tri K)|
          + |((min m ⌈((K : ℝ) + 1) * x⌉₊ : ℝ) - x * m)| := by
        rw [hsplit]; exact abs_add_le _ _
    _ ≤ (K : ℝ) + (K : ℝ) := add_le_add hmain habs
    _ = 2 * K := by ring

lemma blk_sq_le (N : ℕ) : blk N * blk N ≤ 2 * N := by
  have h1 := (blk_spec N).1
  have h2 := two_mul_tri (blk N)
  nlinarith [Nat.le_of_lt_succ (Nat.lt_succ_of_le (le_refl (blk N)))]

lemma blk_le_sqrt (N : ℕ) : (blk N : ℝ) ≤ Real.sqrt (2 * N) := by
  have h : ((blk N : ℝ)) ^ 2 ≤ 2 * N := by
    have := blk_sq_le N
    have : ((blk N * blk N : ℕ) : ℝ) ≤ ((2 * N : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this
    nlinarith [this]
  exact Real.le_sqrt_of_sq_le h

lemma cnt_error_sqrt (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (N : ℕ) :
    |(cnt x N : ℝ) - x * N| ≤ 2 * Real.sqrt (2 * N) := by
  have h1 := cnt_error x hx0 hx1 N
  have h2 := blk_le_sqrt N
  linarith

lemma tendsto_cnt (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Filter.Tendsto (fun N : ℕ => (cnt x N : ℝ) / N) Filter.atTop (nhds x) := by
  have hg : Filter.Tendsto (fun N : ℕ => 2 * Real.sqrt 2 / Real.sqrt N)
      Filter.atTop (nhds 0) := by
    refine Filter.Tendsto.div_atTop tendsto_const_nhds ?_
    exact Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hb : ∀ᶠ N : ℕ in Filter.atTop,
      ‖(cnt x N : ℝ) / N - x‖ ≤ 2 * Real.sqrt 2 / Real.sqrt N := by
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hsqrtN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
    have h := cnt_error_sqrt x hx0 hx1 N
    have hsq : Real.sqrt (2 * N) = Real.sqrt 2 * Real.sqrt N :=
      Real.sqrt_mul (by norm_num) _
    have hNN : (N : ℝ) = Real.sqrt N * Real.sqrt N :=
      (Real.mul_self_sqrt (le_of_lt hN0)).symm
    have heq : ‖(cnt x N : ℝ) / N - x‖ = |(cnt x N : ℝ) - x * N| / N := by
      rw [Real.norm_eq_abs, ← abs_of_pos hN0, ← abs_div, abs_of_pos hN0]
      congr 1
      field_simp
    rw [heq]
    rw [div_le_div_iff₀ hN0 hsqrtN]
    calc |(cnt x N : ℝ) - x * N| * Real.sqrt N
        ≤ (2 * (Real.sqrt 2 * Real.sqrt N)) * Real.sqrt N := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hsqrtN)
          rw [← hsq]; exact h
      _ = 2 * Real.sqrt 2 * (Real.sqrt N * Real.sqrt N) := by ring
      _ = 2 * Real.sqrt 2 * N := by rw [← hNN]
  have hzero : Filter.Tendsto (fun N : ℕ => (cnt x N : ℝ) / N - x)
      Filter.atTop (nhds 0) := squeeze_zero_norm' hb hg
  have := hzero.add_const x
  simpa using this

lemma card_Ico_eq (a b : ℝ) (hab : a ≤ b) (N : ℕ) :
    (((Finset.range N).filter fun n => Int.fract (useq n) ∈ Set.Ico a b).card : ℝ)
      = (cnt b N : ℝ) - (cnt a N : ℝ) := by
  have hsub : ((Finset.range N).filter fun n => useq n < a) ⊆
      ((Finset.range N).filter fun n => useq n < b) := by
    intro n hn
    simp only [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, lt_of_lt_of_le hn.2 hab⟩
  have hset : ((Finset.range N).filter fun n => Int.fract (useq n) ∈ Set.Ico a b)
      = ((Finset.range N).filter fun n => useq n < b) \
        ((Finset.range N).filter fun n => useq n < a) := by
    ext n
    have hmem := useq_mem n
    rw [Set.mem_Ico] at hmem
    have hf : Int.fract (useq n) = useq n := Int.fract_eq_self.mpr ⟨hmem.1, hmem.2⟩
    simp only [Finset.mem_sdiff, Finset.mem_filter, hf, Set.mem_Ico, not_and, not_lt]
    tauto
  have hle : cnt a N ≤ cnt b N := Finset.card_le_card hsub
  rw [hset, Finset.card_sdiff_of_subset hsub]
  show ((cnt b N - cnt a N : ℕ) : ℝ) = _
  rw [Nat.cast_sub hle]

theorem useq_equidistributed : AsymptoticallyEquidistributedMod1 useq := by
  intro a b ha hab hb
  have hb0 : (0 : ℝ) ≤ b := le_trans ha hab
  have ha1 : a ≤ 1 := le_trans hab hb
  have h1 := tendsto_cnt b hb0 hb
  have h2 := tendsto_cnt a ha ha1
  refine (h1.sub h2).congr fun N => ?_
  rw [card_Ico_eq a b hab N, sub_div]

/-- **Existence of an asymptotically equidistributed sequence.** -/
theorem equidistribution_of_asymptotic_exists :
    ∃ u : ℕ → ℝ, (∀ n, u n ∈ Set.Ico (0 : ℝ) 1) ∧ AsymptoticallyEquidistributedMod1 u :=
  ⟨useq, useq_mem, useq_equidistributed⟩

end Brockian.Equidistribution

