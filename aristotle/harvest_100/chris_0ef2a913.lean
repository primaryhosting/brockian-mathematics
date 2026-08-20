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

/-!
## Overview

The named hypothesis is discharged unconditionally by exhibiting an explicit equidistributed
sequence: the base-`2` van der Corput sequence `vdc`, defined by `vdc n = ((n % 2) + vdc (n / 2))/2`.
Writing `bitRev k n` for the reversal of the lowest `k` binary digits of `n`, one has
`vdc n = (bitRev k n + vdc (n / 2 ^ k)) / 2 ^ k`, so `vdc n` lies in the dyadic interval
`[bitRev k n / 2 ^ k, (bitRev k n + 1) / 2 ^ k)`. Since `bitRev k` is a bijection of
`{0, …, 2 ^ k - 1}` depending only on `n % 2 ^ k`, counting the visits to a dyadic interval
reduces to counting an arithmetic progression, which is handled by the Mathlib lemma
`Nat.count_modEq_card_eq_ceil`. Sandwiching an arbitrary interval between dyadic ones then gives
the discrepancy bound `|#{n < N : vdc n < x} - x * N| ≤ N / 2 ^ k + 2 ^ k`, whence equidistribution.
-/

open Filter Finset
open scoped Topology

namespace Brockian.Equidistribution

/-- A sequence `u : ℕ → ℝ` is equidistributed modulo `1` when, for every subinterval
`[a, b) ⊆ [0, 1)`, the asymptotic frequency with which the fractional parts `Int.fract (u n)`
land in `[a, b)` exists and equals the length `b - a` of the interval. -/
def EquidistributedMod1 (u : ℕ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
    Tendsto (fun N : ℕ => (#{n ∈ Finset.range N | Int.fract (u n) ∈ Set.Ico a b} : ℝ) / N)
      atTop (𝓝 (b - a))

/-- The van der Corput sequence in base `2`: `vdc n` is obtained by reflecting the binary
expansion of `n` about the radix point. -/
noncomputable def vdc : ℕ → ℝ
  | 0 => 0
  | (n + 1) => (((n + 1) % 2 : ℕ) + vdc ((n + 1) / 2)) / 2
decreasing_by exact Nat.div_lt_self (Nat.succ_pos n) one_lt_two

/-- Reversal of the lowest `k` binary digits of `n`. -/
def bitRev : ℕ → ℕ → ℕ
  | 0, _ => 0
  | (k + 1), n => (n % 2) * 2 ^ k + bitRev k (n / 2)

lemma vdc_eq (n : ℕ) : vdc n = (((n % 2 : ℕ) : ℝ) + vdc (n / 2)) / 2 := by
  cases n with
  | zero => simp [vdc]
  | succ m => rw [vdc]

lemma vdc_nonneg (n : ℕ) : 0 ≤ vdc n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h, vdc]
    · rw [vdc_eq]
      have := ih (n / 2) (Nat.div_lt_self h one_lt_two)
      positivity

lemma vdc_lt_one (n : ℕ) : vdc n < 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h, vdc]
    · rw [vdc_eq]
      have h1 := ih (n / 2) (Nat.div_lt_self h one_lt_two)
      have h2 : ((n % 2 : ℕ) : ℝ) ≤ 1 := by
        have : n % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
        exact_mod_cast this
      linarith

lemma bitRev_lt (k n : ℕ) : bitRev k n < 2 ^ k := by
  induction k generalizing n with
  | zero => simp [bitRev]
  | succ k ih =>
    have h1 : n % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
    have h2 := ih (n / 2)
    have h3 : n % 2 * 2 ^ k ≤ 1 * 2 ^ k := Nat.mul_le_mul_right _ h1
    have h4 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    simp only [bitRev]
    omega

lemma bitRev_mod (k n : ℕ) : bitRev k (n % 2 ^ k) = bitRev k n := by
  induction k generalizing n with
  | zero => simp [bitRev]
  | succ k ih =>
    simp only [bitRev]
    have e1 : n % 2 ^ (k + 1) % 2 = n % 2 := by
      rw [Nat.mod_mod_of_dvd]
      exact dvd_pow_self 2 (Nat.succ_ne_zero k)
    have e2 : n % 2 ^ (k + 1) / 2 = n / 2 % 2 ^ k := by
      rw [show (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k by ring, Nat.mod_mul_right_div_self]
    rw [e1, e2, ih]

lemma bitRev_injOn (k : ℕ) {m n : ℕ} (hm : m < 2 ^ k) (hn : n < 2 ^ k)
    (h : bitRev k m = bitRev k n) : m = n := by
  induction k generalizing m n with
  | zero => simp at hm hn; omega
  | succ k ih =>
    simp only [bitRev] at h
    have b1 := bitRev_lt k (m / 2)
    have b2 := bitRev_lt k (n / 2)
    have hm2 : m % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
    have hn2 : n % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
    have hbit1 : m % 2 = n % 2 := by nlinarith
    rw [hbit1] at h
    have hbit2 : bitRev k (m / 2) = bitRev k (n / 2) := by omega
    have hpow : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
    have hdm : m / 2 < 2 ^ k := by omega
    have hdn : n / 2 < 2 ^ k := by omega
    have := ih hdm hdn hbit2
    omega

lemma vdc_split (k n : ℕ) :
    vdc n = ((bitRev k n : ℝ) + vdc (n / 2 ^ k)) / 2 ^ k := by
  induction k generalizing n with
  | zero => simp [bitRev]
  | succ k ih =>
    have e : n / 2 / 2 ^ k = n / 2 ^ (k + 1) := by
      rw [Nat.div_div_eq_div_mul]
      ring_nf
    rw [vdc_eq n, ih (n / 2), e]
    simp only [bitRev]
    push_cast
    have hp : (0 : ℝ) < 2 ^ k := by positivity
    field_simp
    ring

lemma vdc_ge (k n : ℕ) : ((bitRev k n : ℝ)) / 2 ^ k ≤ vdc n := by
  rw [vdc_split k n]
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have := vdc_nonneg (n / 2 ^ k)
  gcongr
  linarith

lemma vdc_lt (k n : ℕ) : vdc n < ((bitRev k n : ℝ) + 1) / 2 ^ k := by
  rw [vdc_split k n]
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have := vdc_lt_one (n / 2 ^ k)
  gcongr

/-- The counting function `#{n < N : vdc n < x}`. -/
noncomputable def cnt (x : ℝ) (N : ℕ) : ℕ := #{n ∈ Finset.range N | vdc n < x}

lemma cnt_mono {x y : ℝ} (h : x ≤ y) (N : ℕ) : cnt x N ≤ cnt y N := by
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
  exact ⟨hn.1, lt_of_lt_of_le hn.2 h⟩

lemma cnt_one (N : ℕ) : cnt 1 N = N := by
  rw [cnt, Finset.filter_true_of_mem (fun n _ => vdc_lt_one n), Finset.card_range]

/-- Counting integers below `N` in a fixed residue class mod `m`, up to an error of `1`. -/
lemma card_filter_mod_eq (m N r : ℕ) (hm : 0 < m) (hr : r < m) :
    |(#{n ∈ Finset.range N | n % m = r} : ℝ) - N / m| ≤ 1 := by
  have hset : {n ∈ Finset.range N | n % m = r} = {x ∈ Finset.range N | x ≡ r [MOD m]} := by
    apply Finset.filter_congr
    intro x _
    simp [Nat.ModEq, Nat.mod_eq_of_lt hr]
  set c : ℕ := #{n ∈ Finset.range N | n % m = r} with hc
  have hceil : (c : ℤ) = ⌈((N : ℚ) - r) / m⌉ := by
    have := Nat.count_modEq_card_eq_ceil N hm r
    rw [Nat.count_eq_card_filter_range, Nat.mod_eq_of_lt hr, ← hset] at this
    exact_mod_cast this
  have h1 : ((N : ℚ) - r) / m ≤ (c : ℚ) := by
    rw [show ((c : ℚ)) = ((c : ℤ) : ℚ) by push_cast; ring, hceil]
    exact_mod_cast Int.le_ceil (((N : ℚ) - r) / m)
  have h2 : (c : ℚ) < ((N : ℚ) - r) / m + 1 := by
    rw [show ((c : ℚ)) = ((c : ℤ) : ℚ) by push_cast; ring, hceil]
    exact_mod_cast Int.ceil_lt_add_one (((N : ℚ) - r) / m)
  have h1' : ((N : ℝ) - r) / m ≤ (c : ℝ) := by exact_mod_cast h1
  have h2' : (c : ℝ) < ((N : ℝ) - r) / m + 1 := by exact_mod_cast h2
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hrR2 : (r : ℝ) < m := by exact_mod_cast hr
  have hsplit : ((N : ℝ) - r) / m = N / m - r / m := by field_simp
  have hlt : (r : ℝ) / m < 1 := by rw [div_lt_one hmR]; exact hrR2
  have hge : (0 : ℝ) ≤ (r : ℝ) / m := by positivity
  rw [hsplit] at h1' h2'
  rw [abs_le]
  constructor <;> linarith

lemma card_filter_mod_mem (m N : ℕ) (hm : 0 < m) (S : Finset ℕ) (hS : ∀ r ∈ S, r < m) :
    |(#{n ∈ Finset.range N | n % m ∈ S} : ℝ) - S.card * N / m| ≤ S.card := by
  have hbi : {n ∈ Finset.range N | n % m ∈ S}
      = S.biUnion (fun r => {n ∈ Finset.range N | n % m = r}) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨x % m, h2, h1, rfl⟩
    · rintro ⟨r, hr, h1, h2⟩; exact ⟨h1, h2 ▸ hr⟩
  have hcard : #{n ∈ Finset.range N | n % m ∈ S}
      = ∑ r ∈ S, #{n ∈ Finset.range N | n % m = r} := by
    rw [hbi, Finset.card_biUnion]
    intro a _ b _ hab
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_filter]
    rintro x ⟨_, rfl⟩ ⟨_, h⟩
    exact hab h
  have key : ((#{n ∈ Finset.range N | n % m ∈ S} : ℕ) : ℝ) - S.card * N / m
      = ∑ r ∈ S, ((#{n ∈ Finset.range N | n % m = r} : ℝ) - N / m) := by
    rw [Finset.sum_sub_distrib, hcard]
    push_cast
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [key]
  calc |∑ r ∈ S, ((#{n ∈ Finset.range N | n % m = r} : ℝ) - N / m)|
      ≤ ∑ r ∈ S, |((#{n ∈ Finset.range N | n % m = r} : ℝ) - N / m)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ S, (1 : ℝ) :=
        Finset.sum_le_sum (fun r hr => card_filter_mod_eq m N r hm (hS r hr))
    _ = S.card := by simp

lemma cnt_dyadic_eq (k t N : ℕ) :
    cnt ((t : ℝ) / 2 ^ k) N = #{n ∈ Finset.range N | bitRev k n < t} := by
  rw [cnt]
  congr 1
  apply Finset.filter_congr
  intro n _
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    have hcast : ((t : ℝ)) ≤ ((bitRev k n : ℝ)) := by exact_mod_cast hcon
    have : ((t : ℝ)) / 2 ^ k ≤ ((bitRev k n : ℝ)) / 2 ^ k := by gcongr
    exact absurd (lt_of_lt_of_le h (le_trans this (vdc_ge k n))) (lt_irrefl _)
  · intro h
    refine lt_of_lt_of_le (vdc_lt k n) ?_
    gcongr
    have : (bitRev k n : ℝ) + 1 ≤ (t : ℝ) := by exact_mod_cast h
    linarith

lemma card_bitRev_lt (k t : ℕ) (ht : t ≤ 2 ^ k) :
    #{r ∈ Finset.range (2 ^ k) | bitRev k r < t} = t := by
  set S := {r ∈ Finset.range (2 ^ k) | bitRev k r < t} with hSdef
  have hinj : Set.InjOn (bitRev k) (S : Set ℕ) := by
    intro a ha b hb hab
    simp only [hSdef, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at ha hb
    exact bitRev_injOn k ha.1 hb.1 hab
  have himg : S.image (bitRev k) = Finset.range t := by
    ext j
    simp only [Finset.mem_image, Finset.mem_range, hSdef, Finset.mem_filter]
    constructor
    · rintro ⟨r, ⟨_, hr2⟩, rfl⟩; exact hr2
    · intro hj
      have hsurj : (Finset.range (2 ^ k)).image (bitRev k) = Finset.range (2 ^ k) := by
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
          obtain ⟨r, _, rfl⟩ := hx
          exact bitRev_lt k r
        · rw [Finset.card_image_of_injOn, Finset.card_range]
          intro a ha b hb hab
          simp only [Finset.coe_range, Set.mem_Iio] at ha hb
          exact bitRev_injOn k ha hb hab
      have hj2 : j ∈ Finset.range (2 ^ k) := Finset.mem_range.mpr (lt_of_lt_of_le hj ht)
      rw [← hsurj] at hj2
      simp only [Finset.mem_image, Finset.mem_range] at hj2
      obtain ⟨r, hr, hrj⟩ := hj2
      exact ⟨r, ⟨hr, by rw [hrj]; exact hj⟩, hrj⟩
  calc S.card = (S.image (bitRev k)).card := (Finset.card_image_of_injOn hinj).symm
    _ = t := by rw [himg, Finset.card_range]

lemma cnt_dyadic_bound (k t N : ℕ) (ht : t ≤ 2 ^ k) :
    |(cnt ((t : ℝ) / 2 ^ k) N : ℝ) - t * N / 2 ^ k| ≤ 2 ^ k := by
  set S := {r ∈ Finset.range (2 ^ k) | bitRev k r < t} with hSdef
  have hScard : S.card = t := card_bitRev_lt k t ht
  have hset : {n ∈ Finset.range N | bitRev k n < t}
      = {n ∈ Finset.range N | n % 2 ^ k ∈ S} := by
    apply Finset.filter_congr
    intro n _
    simp only [hSdef, Finset.mem_filter, Finset.mem_range, bitRev_mod]
    exact ⟨fun h => ⟨Nat.mod_lt _ (Nat.two_pow_pos k), h⟩, fun h => h.2⟩
  have hmain := card_filter_mod_mem (2 ^ k) N (Nat.two_pow_pos k) S
    (fun r hr => by
      simp only [hSdef, Finset.mem_filter, Finset.mem_range] at hr
      exact hr.1)
  rw [hScard] at hmain
  push_cast at hmain
  rw [cnt_dyadic_eq, hset]
  refine le_trans hmain ?_
  exact_mod_cast ht

lemma cnt_bound (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (k N : ℕ) :
    |(cnt x N : ℝ) - x * N| ≤ N / 2 ^ k + 2 ^ k := by
  have hpow : (0 : ℝ) < 2 ^ k := by positivity
  set t : ℕ := ⌊x * 2 ^ k⌋₊ with htdef
  have h1 : (t : ℝ) ≤ x * 2 ^ k := Nat.floor_le (by positivity)
  have h2 : x * 2 ^ k < (t : ℝ) + 1 := Nat.lt_floor_add_one _
  have ht : t < 2 ^ k := by
    have : (t : ℝ) < 2 ^ k := lt_of_le_of_lt h1 (by nlinarith)
    exact_mod_cast this
  have hle1 : (t : ℝ) / 2 ^ k ≤ x := by rw [div_le_iff₀ hpow]; linarith
  have hle2 : x ≤ ((t : ℝ) + 1) / 2 ^ k := by rw [le_div_iff₀ hpow]; linarith
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hm1 : (cnt ((t : ℝ) / 2 ^ k) N : ℝ) ≤ (cnt x N : ℝ) := by
    exact_mod_cast cnt_mono hle1 N
  have hm2 : (cnt x N : ℝ) ≤ (cnt (((t : ℝ) + 1) / 2 ^ k) N : ℝ) := by
    have h := cnt_mono hle2 N
    exact_mod_cast h
  have b1 := abs_le.mp (cnt_dyadic_bound k t N (le_of_lt ht))
  have b2 := abs_le.mp (cnt_dyadic_bound k (t + 1) N ht)
  push_cast at b2
  have key1 : x * N ≤ ((t : ℝ) + 1) * N / 2 ^ k := by
    have hmul := mul_le_mul_of_nonneg_right hle2 hN
    calc x * N ≤ (((t : ℝ) + 1) / 2 ^ k) * N := hmul
      _ = ((t : ℝ) + 1) * N / 2 ^ k := by ring
  have key2 : (t : ℝ) * N / 2 ^ k ≤ x * N := by
    have hmul := mul_le_mul_of_nonneg_right hle1 hN
    calc (t : ℝ) * N / 2 ^ k = ((t : ℝ) / 2 ^ k) * N := by ring
      _ ≤ x * N := hmul
  have hring : ((t : ℝ) + 1) * N / 2 ^ k = (t : ℝ) * N / 2 ^ k + N / 2 ^ k := by ring
  rw [abs_le]
  constructor <;> linarith [b1.1, b2.2]

lemma tendsto_cnt (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Tendsto (fun N : ℕ => (cnt x N : ℝ) / N) atTop (𝓝 x) := by
  rcases eq_or_lt_of_le hx1 with rfl | hlt
  · have hev : (fun _ : ℕ => (1 : ℝ)) =ᶠ[atTop] fun N : ℕ => (cnt 1 N : ℝ) / N := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      rw [cnt_one]
      field_simp
    exact tendsto_const_nhds.congr' hev
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨k, hk⟩ : ∃ k : ℕ, ((1 : ℝ) / 2) ^ k < ε / 2 :=
      exists_pow_lt_of_lt_one (by linarith) (by norm_num)
    obtain ⟨M, hM⟩ := exists_nat_gt ((2 : ℝ) ^ k * 2 / ε)
    refine ⟨max M 1, fun N hN => ?_⟩
    have hN1 : 1 ≤ N := le_trans (le_max_right M 1) hN
    have hNM : (M : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_left M 1) hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have hpow : (0 : ℝ) < 2 ^ k := by positivity
    have hbound := cnt_bound x hx0 hlt k N
    have hkk : (1 : ℝ) / 2 ^ k < ε / 2 := by
      rw [div_pow] at hk; simpa using hk
    have h2k : (2 : ℝ) ^ k / N < ε / 2 := by
      rw [div_lt_iff₀ hNpos]
      have h0 : (2 : ℝ) ^ k * 2 / ε < N := lt_of_lt_of_le hM hNM
      rw [div_lt_iff₀ hε] at h0
      linarith
    rw [Real.dist_eq]
    have heq : (cnt x N : ℝ) / N - x = ((cnt x N : ℝ) - x * N) / N := by field_simp
    rw [heq, abs_div, abs_of_pos hNpos]
    calc |(cnt x N : ℝ) - x * N| / N ≤ ((N : ℝ) / 2 ^ k + 2 ^ k) / N := by gcongr
      _ = 1 / 2 ^ k + 2 ^ k / N := by field_simp
      _ < ε := by linarith

lemma card_Ico_eq (a b : ℝ) (hab : a ≤ b) (N : ℕ) :
    (#{n ∈ Finset.range N | vdc n ∈ Set.Ico a b} : ℝ) = (cnt b N : ℝ) - cnt a N := by
  have hsub : {n ∈ Finset.range N | vdc n < a} ⊆ {n ∈ Finset.range N | vdc n < b} := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
    exact ⟨hn.1, lt_of_lt_of_le hn.2 hab⟩
  have hset : {n ∈ Finset.range N | vdc n ∈ Set.Ico a b}
      = {n ∈ Finset.range N | vdc n < b} \ {n ∈ Finset.range N | vdc n < a} := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range, Set.mem_Ico, not_and,
      not_lt]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h3⟩, fun _ => h2⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h3 h1, h2⟩
  rw [hset, Finset.card_sdiff_of_subset hsub, cnt, cnt]
  have hcard := Finset.card_le_card hsub
  push_cast [Nat.cast_sub hcard]
  ring

lemma vdc_equidistributed : EquidistributedMod1 vdc := by
  intro a b ha hab hb
  have hb0 : 0 ≤ b := le_trans ha hab
  have ha1 : a ≤ 1 := le_trans hab hb
  have hfract : ∀ n : ℕ, Int.fract (vdc n) = vdc n := fun n =>
    Int.fract_eq_self.mpr ⟨vdc_nonneg n, vdc_lt_one n⟩
  have hfun : ∀ N : ℕ,
      (#{n ∈ Finset.range N | Int.fract (vdc n) ∈ Set.Ico a b} : ℝ) / N
        = (cnt b N : ℝ) / N - (cnt a N : ℝ) / N := by
    intro N
    simp only [hfract]
    rw [card_Ico_eq a b hab N, sub_div]
  exact Tendsto.congr (fun N => (hfun N).symm)
    ((tendsto_cnt b hb0 hb).sub (tendsto_cnt a ha ha1))

/-- **Existence of an equidistributed sequence.** There is a sequence of real numbers whose
fractional parts are equidistributed modulo `1`: for every subinterval `[a, b) ⊆ [0, 1)` the
asymptotic frequency of visits exists and equals `b - a`. -/
theorem equidistribution_of_asymptotic_exists : ∃ u : ℕ → ℝ, EquidistributedMod1 u :=
  ⟨vdc, vdc_equidistributed⟩

end Brockian.Equidistribution

