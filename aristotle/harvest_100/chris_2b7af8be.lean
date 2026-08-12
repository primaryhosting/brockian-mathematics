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
# Config Count Density Of BV
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_density_of_BV
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Topology Set MeasureTheory
open scoped BigOperators Classical

namespace Brockian.EquidistributionBVReduction

/-- The number of indices `n < N` whose fractional part `Int.fract (x n)` lies in `S`:
the count of "configurations" of the first `N` terms of the sequence inside the window `S`. -/
noncomputable def configCount (x : ℕ → ℝ) (S : Set ℝ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun n => Int.fract (x n) ∈ S).card

/-- The sequence `x` is equidistributed mod one: for every window `[a, b) ⊆ [0,1]`,
the density of configuration counts in that window is its length. -/
def EquidistributedMod1 (x : ℕ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
    Tendsto (fun N : ℕ => (configCount x (Set.Ico a b) N : ℝ) / N) atTop (𝓝 (b - a))

section Partition

variable {x : ℕ → ℝ} {k : ℕ}

lemma fract_mem_Icc (x : ℕ → ℝ) (n : ℕ) : Int.fract (x n) ∈ Icc (0 : ℝ) 1 :=
  ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩

lemma div_mem_Icc (hk : 0 < k) {i : ℕ} (hi : i ≤ k) : ((i : ℝ) / k) ∈ Icc (0 : ℝ) 1 := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨by positivity, ?_⟩
  rw [div_le_one hk']
  exact_mod_cast hi

/-- The index of the window of the `k`-fold equal partition of `[0,1)` containing the
`n`-th configuration. -/
noncomputable def idx (x : ℕ → ℝ) (k n : ℕ) : ℕ := ⌊(k : ℝ) * Int.fract (x n)⌋₊

lemma idx_eq_iff (x : ℕ → ℝ) (hk : 0 < k) (i n : ℕ) :
    idx x k n = i ↔ Int.fract (x n) ∈ Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h0 : (0 : ℝ) ≤ (k : ℝ) * Int.fract (x n) := by
    have := Int.fract_nonneg (x n); positivity
  rw [idx, Nat.floor_eq_iff h0]
  simp only [Set.mem_Ico, div_le_iff₀ hk', lt_div_iff₀ hk']
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith

lemma idx_mem_range (x : ℕ → ℝ) (hk : 0 < k) (n : ℕ) : idx x k n ∈ Finset.range k := by
  have h0 : (0 : ℝ) ≤ (k : ℝ) * Int.fract (x n) := by
    have := Int.fract_nonneg (x n); positivity
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 : (k : ℝ) * Int.fract (x n) < (k : ℕ) := by
    have := Int.fract_lt_one (x n); nlinarith
  simpa [idx, Finset.mem_range] using (Nat.floor_lt h0).2 h1

/-- The configuration count of the `i`-th window is the cardinality of the `i`-th fiber
of the index map. -/
lemma configCount_eq_card_fiber (x : ℕ → ℝ) (hk : 0 < k) (i N : ℕ) :
    configCount x (Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)) N
      = ((Finset.range N).filter fun n => idx x k n = i).card := by
  rw [configCount]
  congr 1
  ext n
  simp [Finset.mem_filter, idx_eq_iff x hk i n]

/-- The `k` equal windows partition the first `N` configurations. -/
lemma sum_configCount (x : ℕ → ℝ) (hk : 0 < k) (N : ℕ) :
    ∑ i ∈ Finset.range k, configCount x (Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)) N = N := by
  have h := Finset.card_eq_sum_card_fiberwise
    (f := fun n => idx x k n) (s := Finset.range N) (t := Finset.range k)
    (fun n _ => idx_mem_range x hk n)
  simp only [Finset.card_range] at h
  refine (Finset.sum_congr rfl fun i _ => ?_).trans h.symm
  exact configCount_eq_card_fiber x hk i N

lemma sum_fiberwise (x : ℕ → ℝ) (hk : 0 < k) (N : ℕ) (F : ℕ → ℝ) :
    ∑ i ∈ Finset.range k, ∑ n ∈ (Finset.range N).filter (fun n => idx x k n = i), F n
      = ∑ n ∈ Finset.range N, F n :=
  Finset.sum_fiberwise_of_maps_to (fun n _ => idx_mem_range x hk n) F

/-- Lower Riemann sum bound for a monotone integrand. -/
lemma lower_sum_le {g : ℝ → ℝ} (hg : MonotoneOn g (Icc (0 : ℝ) 1)) (x : ℕ → ℝ) (hk : 0 < k)
    (N : ℕ) :
    ∑ i ∈ Finset.range k,
        (configCount x (Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)) N : ℝ) * g ((i : ℝ) / k)
      ≤ ∑ n ∈ Finset.range N, g (Int.fract (x n)) := by
  rw [← sum_fiberwise x hk N (fun n => g (Int.fract (x n)))]
  refine Finset.sum_le_sum fun i hi => ?_
  have hik : i ≤ k := (Finset.mem_range.1 hi).le
  rw [configCount_eq_card_fiber x hk i N, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun n hn => ?_
  have hidx : idx x k n = i := (Finset.mem_filter.1 hn).2
  have hmem := (idx_eq_iff x hk i n).1 hidx
  exact hg (div_mem_Icc hk hik) (fract_mem_Icc x n) hmem.1

/-- Upper Riemann sum bound for a monotone integrand. -/
lemma le_upper_sum {g : ℝ → ℝ} (hg : MonotoneOn g (Icc (0 : ℝ) 1)) (x : ℕ → ℝ) (hk : 0 < k)
    (N : ℕ) :
    ∑ n ∈ Finset.range N, g (Int.fract (x n))
      ≤ ∑ i ∈ Finset.range k,
        (configCount x (Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)) N : ℝ) * g (((i : ℝ) + 1) / k) := by
  rw [← sum_fiberwise x hk N (fun n => g (Int.fract (x n)))]
  refine Finset.sum_le_sum fun i hi => ?_
  have hik : i + 1 ≤ k := Finset.mem_range.1 hi
  have hik' : ((i : ℝ) + 1) / k ∈ Icc (0 : ℝ) 1 := by
    have := div_mem_Icc (k := k) hk hik
    push_cast at this
    exact this
  rw [configCount_eq_card_fiber x hk i N, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun n hn => ?_
  have hidx : idx x k n = i := (Finset.mem_filter.1 hn).2
  have hmem := (idx_eq_iff x hk i n).1 hidx
  exact hg (fract_mem_Icc x n) hik' hmem.2.le

end Partition

section Integral

variable {g : ℝ → ℝ} {k : ℕ}

lemma node_le (hk : 0 < k) (i : ℕ) : (i : ℝ) / k ≤ ((i : ℝ) + 1) / k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  gcongr
  linarith

lemma Icc_node_subset (hk : 0 < k) {i : ℕ} (hi : i < k) :
    Icc ((i : ℝ) / k) (((i : ℝ) + 1) / k) ⊆ Icc (0 : ℝ) 1 := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 : (0 : ℝ) ≤ (i : ℝ) / k := by positivity
  have h2 : ((i : ℝ) + 1) / k ≤ 1 := by
    rw [div_le_one hk']
    have : (i : ℝ) + 1 ≤ k := by exact_mod_cast hi
    linarith
  exact Icc_subset_Icc h1 h2

lemma intervalIntegrable_node (hg : MonotoneOn g (Icc (0 : ℝ) 1)) (hk : 0 < k) {i : ℕ}
    (hi : i < k) : IntervalIntegrable g volume ((i : ℝ) / k) (((i : ℝ) + 1) / k) := by
  refine (hg.mono ?_).intervalIntegrable
  rw [uIcc_of_le (node_le hk i)]
  exact Icc_node_subset hk hi

lemma sum_integral_nodes (hg : MonotoneOn g (Icc (0 : ℝ) 1)) (hk : 0 < k) :
    ∑ i ∈ Finset.range k, ∫ t in ((i : ℝ) / k)..(((i : ℝ) + 1) / k), g t
      = ∫ t in (0 : ℝ)..1, g t := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := g)
    (a := fun i : ℕ => (i : ℝ) / k) (n := k) (by
      intro i hi
      have := intervalIntegrable_node hg hk hi
      push_cast
      exact this)
  simpa [div_self (ne_of_gt hk')] using this

lemma lower_sum_le_integral (hg : MonotoneOn g (Icc (0 : ℝ) 1)) (hk : 0 < k) :
    ∑ i ∈ Finset.range k, g ((i : ℝ) / k) / k ≤ ∫ t in (0 : ℝ)..1, g t := by
  rw [← sum_integral_nodes hg hk]
  refine Finset.sum_le_sum fun i hi => ?_
  have hik := Finset.mem_range.1 hi
  have hml : ((i : ℝ) / k) ∈ Icc (0 : ℝ) 1 :=
    Icc_node_subset hk hik ⟨le_refl _, node_le hk i⟩
  have hmono : ∀ t ∈ Icc ((i : ℝ) / k) (((i : ℝ) + 1) / k), g ((i : ℝ) / k) ≤ g t := fun t ht =>
    hg hml (Icc_node_subset hk hik ht) ht.1
  have hcalc := intervalIntegral.integral_mono_on (μ := volume) (f := fun _ => g ((i : ℝ) / k))
    (g := g) (node_le hk i) intervalIntegrable_const (intervalIntegrable_node hg hk hik) hmono
  rw [intervalIntegral.integral_const] at hcalc
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hw : (((i : ℝ) + 1) / k - (i : ℝ) / k) = 1 / k := by field_simp; ring
  rw [hw] at hcalc
  simpa [smul_eq_mul, one_div, div_eq_inv_mul] using hcalc

lemma integral_le_upper_sum (hg : MonotoneOn g (Icc (0 : ℝ) 1)) (hk : 0 < k) :
    (∫ t in (0 : ℝ)..1, g t) ≤ ∑ i ∈ Finset.range k, g (((i : ℝ) + 1) / k) / k := by
  rw [← sum_integral_nodes hg hk]
  refine Finset.sum_le_sum fun i hi => ?_
  have hik := Finset.mem_range.1 hi
  have hmr : (((i : ℝ) + 1) / k) ∈ Icc (0 : ℝ) 1 :=
    Icc_node_subset hk hik ⟨node_le hk i, le_refl _⟩
  have hmono : ∀ t ∈ Icc ((i : ℝ) / k) (((i : ℝ) + 1) / k), g t ≤ g (((i : ℝ) + 1) / k) :=
    fun t ht => hg (Icc_node_subset hk hik ht) hmr ht.2
  have hcalc := intervalIntegral.integral_mono_on (μ := volume) (f := g)
    (g := fun _ => g (((i : ℝ) + 1) / k)) (node_le hk i) (intervalIntegrable_node hg hk hik)
    intervalIntegrable_const hmono
  rw [intervalIntegral.integral_const] at hcalc
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hw : (((i : ℝ) + 1) / k - (i : ℝ) / k) = 1 / k := by field_simp; ring
  rw [hw] at hcalc
  simpa [smul_eq_mul, one_div, div_eq_inv_mul] using hcalc

lemma upper_sub_lower (hk : 0 < k) :
    (∑ i ∈ Finset.range k, g (((i : ℝ) + 1) / k) / k)
        - (∑ i ∈ Finset.range k, g ((i : ℝ) / k) / k) = (g 1 - g 0) / k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [← Finset.sum_sub_distrib]
  have h : ∀ i ∈ Finset.range k,
      g (((i : ℝ) + 1) / k) / k - g ((i : ℝ) / k) / k
        = (fun j : ℕ => g ((j : ℝ) / k) / k) (i + 1) - (fun j : ℕ => g ((j : ℝ) / k) / k) i := by
    intro i _
    simp only
    push_cast
    ring
  rw [Finset.sum_congr rfl h, Finset.sum_range_sub (fun j : ℕ => g ((j : ℝ) / k) / k) k]
  simp [div_self (ne_of_gt hk')]
  ring

end Integral

/-- Densities of the `k` equal windows, weighted arbitrarily, converge to the average of
the weights. -/
lemma tendsto_weighted_density {x : ℕ → ℝ} (hx : EquidistributedMod1 x) {k : ℕ} (hk : 0 < k)
    (w : ℕ → ℝ) :
    Tendsto (fun N : ℕ =>
        (∑ i ∈ Finset.range k,
          (configCount x (Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)) N : ℝ) * w i) / N)
      atTop (𝓝 (∑ i ∈ Finset.range k, w i / k)) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  simp only [Finset.sum_div]
  refine tendsto_finset_sum _ fun i hi => ?_
  have hik := Finset.mem_range.1 hi
  have h1 : (0 : ℝ) ≤ (i : ℝ) / k := by positivity
  have h3 : ((i : ℝ) + 1) / k ≤ 1 := by
    rw [div_le_one hk']
    have : (i : ℝ) + 1 ≤ k := by exact_mod_cast hik
    linarith
  have hlim := hx ((i : ℝ) / k) (((i : ℝ) + 1) / k) h1 (node_le hk i) h3
  have hw : ((i : ℝ) + 1) / k - (i : ℝ) / k = 1 / k := by field_simp; ring
  rw [hw] at hlim
  have hmul := hlim.mul_const (w i)
  have heq : (fun N : ℕ =>
      ((configCount x (Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)) N : ℝ) / N) * w i)
      = fun N : ℕ =>
      ((configCount x (Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)) N : ℝ) * w i) / N := by
    funext N; ring
  rw [heq] at hmul
  have hval : 1 / (k : ℝ) * w i = w i / k := by ring
  rwa [hval] at hmul

/-- Birkhoff averages along an equidistributed sequence converge to the integral,
for a monotone integrand. -/
lemma tendsto_average_of_monotoneOn {x : ℕ → ℝ} (hx : EquidistributedMod1 x) {g : ℝ → ℝ}
    (hg : MonotoneOn g (Icc (0 : ℝ) 1)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, g (Int.fract (x n))) / N) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, g t)) := by
  set I : ℝ := ∫ t in (0 : ℝ)..1, g t with hI
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hD : 0 ≤ g 1 - g 0 :=
    sub_nonneg.2 (hg (by norm_num) (by norm_num) zero_le_one)
  obtain ⟨k, hkgt⟩ := exists_nat_gt (2 * (g 1 - g 0) / ε)
  have hknn : (0 : ℝ) ≤ 2 * (g 1 - g 0) / ε := by positivity
  have hk0 : 0 < k := by
    by_contra h
    push_neg at h
    interval_cases k
    · simp at hkgt; linarith
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk0
  have hkD : (g 1 - g 0) / k < ε / 2 := by
    rw [div_lt_iff₀ hε] at hkgt
    rw [div_lt_iff₀ hk']
    linarith
  set L : ℝ := ∑ i ∈ Finset.range k, g ((i : ℝ) / k) / k with hLdef
  set U : ℝ := ∑ i ∈ Finset.range k, g (((i : ℝ) + 1) / k) / k with hUdef
  have hLI : L ≤ I := lower_sum_le_integral hg hk0
  have hIU : I ≤ U := integral_le_upper_sum hg hk0
  have hUL : U - L = (g 1 - g 0) / k := upper_sub_lower hk0
  have hlow := tendsto_weighted_density hx hk0 (fun i : ℕ => g ((i : ℝ) / k))
  have hupp := tendsto_weighted_density hx hk0 (fun i : ℕ => g (((i : ℝ) + 1) / k))
  rw [Metric.tendsto_atTop] at hlow hupp
  obtain ⟨N1, hN1⟩ := hlow (ε / 4) (by linarith)
  obtain ⟨N2, hN2⟩ := hupp (ε / 4) (by linarith)
  refine ⟨max (max N1 N2) 1, fun N hN => ?_⟩
  have hNN1 : N1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNN2 : N2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN0 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  have hl := hN1 N hNN1
  have hu := hN2 N hNN2
  rw [Real.dist_eq, abs_lt] at hl hu
  have hlow_le : (∑ i ∈ Finset.range k,
        (configCount x (Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)) N : ℝ) * g ((i : ℝ) / k)) / N
      ≤ (∑ n ∈ Finset.range N, g (Int.fract (x n))) / N := by
    gcongr
    exact lower_sum_le hg x hk0 N
  have hle_upp : (∑ n ∈ Finset.range N, g (Int.fract (x n))) / N
      ≤ (∑ i ∈ Finset.range k,
        (configCount x (Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)) N : ℝ)
          * g (((i : ℝ) + 1) / k)) / N := by
    gcongr
    exact le_upper_sum hg x hk0 N
  rw [Real.dist_eq, abs_lt]
  constructor
  · linarith [hl.1, hu.2]
  · linarith [hl.1, hu.2]

/-- **Config count density for functions of bounded variation.**
If the configuration counts of `x` have the expected densities on all windows
(`EquidistributedMod1`), then the Birkhoff averages along `x` of any function of bounded
variation on `[0,1]` converge to its integral. -/
theorem configCount_density_of_BV {x : ℕ → ℝ} (hx : EquidistributedMod1 x) {f : ℝ → ℝ}
    (hf : BoundedVariationOn f (Icc (0 : ℝ) 1)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (Int.fract (x n))) / N) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, f t)) := by
  obtain ⟨p, q, hp, hq, rfl⟩ :=
    hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  have hpi : IntervalIntegrable p volume 0 1 := by
    refine MonotoneOn.intervalIntegrable ?_
    rwa [uIcc_of_le zero_le_one]
  have hqi : IntervalIntegrable q volume 0 1 := by
    refine MonotoneOn.intervalIntegrable ?_
    rwa [uIcc_of_le zero_le_one]
  have hint : (∫ t in (0 : ℝ)..1, (p - q) t)
      = (∫ t in (0 : ℝ)..1, p t) - ∫ t in (0 : ℝ)..1, q t := by
    simp only [Pi.sub_apply]
    exact intervalIntegral.integral_sub hpi hqi
  rw [hint]
  have hsum : ∀ N : ℕ, (∑ n ∈ Finset.range N, (p - q) (Int.fract (x n))) / N
      = (∑ n ∈ Finset.range N, p (Int.fract (x n))) / N
        - (∑ n ∈ Finset.range N, q (Int.fract (x n))) / N := by
    intro N
    simp [Pi.sub_apply, Finset.sum_sub_distrib, sub_div]
  simp only [hsum]
  exact (tendsto_average_of_monotoneOn hx hp).sub (tendsto_average_of_monotoneOn hx hq)

end Brockian.EquidistributionBVReduction

