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
# Config Count Density Of BV
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_density_of_BV
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open MeasureTheory Filter Topology Set

namespace Brockian.EquidistributionBVReduction

open scoped Classical in
/-- `configCount x A N` is the number of indices `n < N` whose orbit point `x n`,
reduced mod `1`, lands in the configuration set `A`. -/
noncomputable def configCount (x : ℕ → ℝ) (A : Set ℝ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => Int.fract (x n) ∈ A)).card

/-- `x : ℕ → ℝ` is equidistributed mod `1`: for every subinterval `[a, b) ⊆ [0,1]`
the proportion of the first `N` points landing in `[a, b)` tends to its length. -/
def EquidistributedMod1 (x : ℕ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
    Tendsto (fun N : ℕ => (configCount x (Set.Ico a b) N : ℝ) / N) atTop (𝓝 (b - a))

section Monotone

variable {x : ℕ → ℝ} {g : ℝ → ℝ}

/-- Membership in the `j`-th dyadic-style fibre of the partition of `[0,1)` into `K`
equal pieces is detected by the floor function. -/
lemma floor_mul_eq_iff_mem_Ico {K : ℕ} (hK : 0 < K) (j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ⌊(K : ℝ) * t⌋₊ = j ↔ t ∈ Set.Ico ((j : ℝ) / K) (((j : ℝ) + 1) / K) := by
  have hK' : (0:ℝ) < K := by exact_mod_cast hK
  rw [Nat.floor_eq_iff (by positivity)]
  simp only [Set.mem_Ico, div_le_iff₀ hK', lt_div_iff₀ hK']
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith

/-- The `⌊K t⌋₊ = j` fibre of `Finset.range N` has exactly `configCount` many elements for
the interval `[j/K, (j+1)/K)`. -/
lemma configCount_eq_card_fiber (x : ℕ → ℝ) {K : ℕ} (hK : 0 < K) (j N : ℕ) :
    configCount x (Set.Ico ((j : ℝ) / K) (((j : ℝ) + 1) / K)) N
      = ((Finset.range N).filter (fun n => ⌊(K : ℝ) * Int.fract (x n)⌋₊ = j)).card := by
  classical
  simp only [configCount]
  congr 1
  ext n
  simp [floor_mul_eq_iff_mem_Ico hK j (Int.fract_nonneg (x n))]

lemma floor_mem_range (x : ℕ → ℝ) {K : ℕ} (hK : 0 < K) (N : ℕ) :
    ∀ n ∈ Finset.range N, ⌊(K : ℝ) * Int.fract (x n)⌋₊ ∈ Finset.range K := by
  have hK' : (0:ℝ) < K := by exact_mod_cast hK
  intro n _
  simp only [Finset.mem_range]
  rw [Nat.floor_lt (mul_nonneg hK'.le (Int.fract_nonneg _))]
  nlinarith [Int.fract_lt_one (x n), Int.fract_nonneg (x n)]

lemma div_mem_Icc_of_le {K j : ℕ} (hK : 0 < K) (hj : j ≤ K) :
    ((j : ℝ) / K) ∈ Set.Icc (0:ℝ) 1 := by
  have hK' : (0:ℝ) < K := by exact_mod_cast hK
  refine ⟨by positivity, ?_⟩
  rw [div_le_one hK']
  exact_mod_cast hj

/-- Lower Riemann-type bound for the orbit sum of a monotone function. -/
lemma sum_fiber_lower (x : ℕ → ℝ) (hg : MonotoneOn g (Set.Icc (0:ℝ) 1)) {K : ℕ} (hK : 0 < K)
    (N : ℕ) :
    ∑ j ∈ Finset.range K,
        (configCount x (Set.Ico ((j : ℝ) / K) (((j : ℝ) + 1) / K)) N : ℝ) * g ((j : ℝ) / K)
      ≤ ∑ n ∈ Finset.range N, g (Int.fract (x n)) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (floor_mem_range x hK N) (fun n => g (Int.fract (x n)))]
  refine Finset.sum_le_sum ?_
  intro j hj
  simp only [Finset.mem_range] at hj
  rw [configCount_eq_card_fiber x hK j N]
  have hmem := div_mem_Icc_of_le hK hj.le
  have key := Finset.card_nsmul_le_sum
    ((Finset.range N).filter (fun n => ⌊(K:ℝ) * Int.fract (x n)⌋₊ = j))
    (fun n => g (Int.fract (x n))) (g ((j:ℝ)/K)) ?_
  · simpa [nsmul_eq_mul] using key
  · intro n hn
    simp only [Finset.mem_filter] at hn
    have h2 := (floor_mul_eq_iff_mem_Ico hK j (Int.fract_nonneg (x n))).1 hn.2
    exact hg hmem ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩ h2.1

/-- Upper Riemann-type bound for the orbit sum of a monotone function. -/
lemma sum_fiber_upper (x : ℕ → ℝ) (hg : MonotoneOn g (Set.Icc (0:ℝ) 1)) {K : ℕ} (hK : 0 < K)
    (N : ℕ) :
    ∑ n ∈ Finset.range N, g (Int.fract (x n))
      ≤ ∑ j ∈ Finset.range K,
        (configCount x (Set.Ico ((j : ℝ) / K) (((j : ℝ) + 1) / K)) N : ℝ)
          * g (((j : ℝ) + 1) / K) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (floor_mem_range x hK N) (fun n => g (Int.fract (x n)))]
  refine Finset.sum_le_sum ?_
  intro j hj
  simp only [Finset.mem_range] at hj
  rw [configCount_eq_card_fiber x hK j N]
  have hmem : (((j : ℝ) + 1) / K) ∈ Set.Icc (0:ℝ) 1 := by
    have := div_mem_Icc_of_le hK hj
    simpa using this
  have key := Finset.sum_le_card_nsmul
    ((Finset.range N).filter (fun n => ⌊(K:ℝ) * Int.fract (x n)⌋₊ = j))
    (fun n => g (Int.fract (x n))) (g (((j:ℝ)+1)/K)) ?_
  · simpa [nsmul_eq_mul] using key
  · intro n hn
    simp only [Finset.mem_filter] at hn
    have h2 := (floor_mul_eq_iff_mem_Ico hK j (Int.fract_nonneg (x n))).1 hn.2
    exact hg ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩ hmem h2.2.le

lemma lower_riemann_le_integral (hg : MonotoneOn g (Set.Icc (0:ℝ) 1)) {K : ℕ} (hK : 0 < K) :
    ∑ j ∈ Finset.range K, (1 / (K : ℝ)) * g ((j : ℝ) / K) ≤ ∫ t in (0:ℝ)..1, g t := by
  have hK' : (0:ℝ) < K := by exact_mod_cast hK
  set a : ℕ → ℝ := fun j => (j:ℝ)/K with ha
  have hale : ∀ j : ℕ, a j ≤ a (j+1) := by
    intro j; simp only [ha]; push_cast
    rw [div_le_div_iff_of_pos_right hK']; linarith
  have hsub : ∀ j : ℕ, j < K → Set.Icc (a j) (a (j+1)) ⊆ Set.Icc (0:ℝ) 1 := by
    intro j hj
    apply Set.Icc_subset_Icc
    · simp only [ha]; positivity
    · simp only [ha]; push_cast
      rw [div_le_one hK']
      have : (j:ℝ) + 1 ≤ K := by exact_mod_cast hj
      linarith
  have hint : ∀ j : ℕ, j < K → IntervalIntegrable g volume (a j) (a (j+1)) := by
    intro j hj
    apply MonotoneOn.intervalIntegrable
    rw [Set.uIcc_of_le (hale j)]
    exact hg.mono (hsub j hj)
  have hsum : ∑ j ∈ Finset.range K, ∫ t in (a j)..(a (j+1)), g t = ∫ t in (a 0)..(a K), g t :=
    intervalIntegral.sum_integral_adjacent_intervals hint
  have h0 : a 0 = 0 := by simp [ha]
  have hKK : a K = 1 := by simp only [ha]; field_simp
  rw [h0, hKK] at hsum
  rw [← hsum]
  refine Finset.sum_le_sum ?_
  intro j hj
  simp only [Finset.mem_range] at hj
  have hcalc : (1 / (K:ℝ)) * g ((j:ℝ)/K) = ∫ _t in (a j)..(a (j+1)), g ((j:ℝ)/K) := by
    rw [intervalIntegral.integral_const]
    simp only [ha, smul_eq_mul]
    push_cast
    field_simp
    ring
  rw [hcalc]
  apply intervalIntegral.integral_mono_on (hale j) intervalIntegrable_const (hint j hj)
  intro t ht
  exact hg (hsub j hj (Set.left_mem_Icc.2 (hale j))) (hsub j hj ht) ht.1

lemma integral_le_upper_riemann (hg : MonotoneOn g (Set.Icc (0:ℝ) 1)) {K : ℕ} (hK : 0 < K) :
    (∫ t in (0:ℝ)..1, g t) ≤ ∑ j ∈ Finset.range K, (1 / (K : ℝ)) * g (((j : ℝ) + 1) / K) := by
  have hK' : (0:ℝ) < K := by exact_mod_cast hK
  set a : ℕ → ℝ := fun j => (j:ℝ)/K with ha
  have hale : ∀ j : ℕ, a j ≤ a (j+1) := by
    intro j; simp only [ha]; push_cast
    rw [div_le_div_iff_of_pos_right hK']; linarith
  have hsub : ∀ j : ℕ, j < K → Set.Icc (a j) (a (j+1)) ⊆ Set.Icc (0:ℝ) 1 := by
    intro j hj
    apply Set.Icc_subset_Icc
    · simp only [ha]; positivity
    · simp only [ha]; push_cast
      rw [div_le_one hK']
      have : (j:ℝ) + 1 ≤ K := by exact_mod_cast hj
      linarith
  have hint : ∀ j : ℕ, j < K → IntervalIntegrable g volume (a j) (a (j+1)) := by
    intro j hj
    apply MonotoneOn.intervalIntegrable
    rw [Set.uIcc_of_le (hale j)]
    exact hg.mono (hsub j hj)
  have hsum : ∑ j ∈ Finset.range K, ∫ t in (a j)..(a (j+1)), g t = ∫ t in (a 0)..(a K), g t :=
    intervalIntegral.sum_integral_adjacent_intervals hint
  have h0 : a 0 = 0 := by simp [ha]
  have hKK : a K = 1 := by simp only [ha]; field_simp
  rw [h0, hKK] at hsum
  rw [← hsum]
  refine Finset.sum_le_sum ?_
  intro j hj
  simp only [Finset.mem_range] at hj
  have hcalc : (1 / (K:ℝ)) * g (((j:ℝ)+1)/K) = ∫ _t in (a j)..(a (j+1)), g (((j:ℝ)+1)/K) := by
    rw [intervalIntegral.integral_const]
    simp only [ha, smul_eq_mul]
    push_cast
    field_simp
    ring
  rw [hcalc]
  apply intervalIntegral.integral_mono_on (hale j) (hint j hj) intervalIntegrable_const
  intro t ht
  have hright : a (j+1) ∈ Set.Icc (0:ℝ) 1 := hsub j hj (Set.right_mem_Icc.2 (hale j))
  have : g t ≤ g (a (j+1)) := hg (hsub j hj ht) hright ht.2
  simpa only [ha, Nat.cast_add, Nat.cast_one] using this

/-- The empirical measures of the `K` partition intervals: their weighted sums converge. -/
lemma tendsto_riemann_sums (hx : EquidistributedMod1 x) {K : ℕ} (hK : 0 < K) (c : ℕ → ℝ) :
    Tendsto (fun N : ℕ => ∑ j ∈ Finset.range K,
        ((configCount x (Set.Ico ((j : ℝ) / K) (((j : ℝ) + 1) / K)) N : ℝ) / N) * c j)
      atTop (𝓝 (∑ j ∈ Finset.range K, (1 / (K:ℝ)) * c j)) := by
  have hK' : (0:ℝ) < K := by exact_mod_cast hK
  refine tendsto_finset_sum _ ?_
  intro j hj
  simp only [Finset.mem_range] at hj
  have hb : ((j:ℝ) + 1) / K ≤ 1 := by
    rw [div_le_one hK']
    have : (j:ℝ) + 1 ≤ K := by exact_mod_cast hj
    linarith
  have hab : (j:ℝ)/K ≤ ((j:ℝ)+1)/K := by
    rw [div_le_div_iff_of_pos_right hK']; linarith
  have h := hx ((j:ℝ)/K) (((j:ℝ)+1)/K) (by positivity) hab hb
  have hlen : ((j:ℝ)+1)/K - (j:ℝ)/K = 1 / K := by field_simp; ring
  rw [hlen] at h
  exact h.mul_const (c j)

/-- Cesàro averages of a function that is monotone on `[0,1]` along an equidistributed
sequence converge to its integral. -/
theorem tendsto_average_of_monotoneOn (hx : EquidistributedMod1 x)
    (hg : MonotoneOn g (Set.Icc (0:ℝ) 1)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, g (Int.fract (x n))) / N)
      atTop (𝓝 (∫ t in (0:ℝ)..1, g t)) := by
  classical
  set I := ∫ t in (0:ℝ)..1, g t with hI
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hg01 : g 0 ≤ g 1 := hg (by norm_num) (by norm_num) (by norm_num)
  -- choose a fine enough partition
  obtain ⟨K, hK1, hKε⟩ : ∃ K : ℕ, 0 < K ∧ (g 1 - g 0) / K < ε / 4 := by
    obtain ⟨K, hK⟩ := exists_nat_gt (max 1 (4 * (g 1 - g 0) / ε))
    have h1 : (1:ℝ) < K := lt_of_le_of_lt (le_max_left _ _) hK
    have h2 : 4 * (g 1 - g 0) / ε < K := lt_of_le_of_lt (le_max_right _ _) hK
    have hK' : (0:ℝ) < K := by linarith
    refine ⟨K, by exact_mod_cast hK', ?_⟩
    rw [div_lt_div_iff₀ hK' (by norm_num : (0:ℝ) < 4)]
    rw [div_lt_iff₀ hε] at h2
    linarith
  have hK' : (0:ℝ) < K := by exact_mod_cast hK1
  set L := ∑ j ∈ Finset.range K, (1 / (K:ℝ)) * g ((j:ℝ)/K) with hL
  set U := ∑ j ∈ Finset.range K, (1 / (K:ℝ)) * g (((j:ℝ)+1)/K) with hU
  have hLI : L ≤ I := lower_riemann_le_integral hg hK1
  have hIU : I ≤ U := integral_le_upper_riemann hg hK1
  have hUL : U - L = (g 1 - g 0) / K := by
    rw [hU, hL, ← Finset.sum_sub_distrib]
    have : ∀ j ∈ Finset.range K,
        (1 / (K:ℝ)) * g (((j:ℝ)+1)/K) - (1 / (K:ℝ)) * g ((j:ℝ)/K)
          = (1 / (K:ℝ)) * ((fun m : ℕ => g ((m:ℝ)/K)) (j+1) - (fun m : ℕ => g ((m:ℝ)/K)) j) := by
      intro j _
      simp only
      push_cast
      ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, Finset.sum_range_sub
      (fun m : ℕ => g ((m:ℝ)/K))]
    simp only [Nat.cast_zero, zero_div]
    rw [div_self hK'.ne']
    ring
  -- the two empirical Riemann sums converge
  have hSL := tendsto_riemann_sums (x := x) hx hK1 (fun j => g ((j:ℝ)/K))
  have hSU := tendsto_riemann_sums (x := x) hx hK1 (fun j => g (((j:ℝ)+1)/K))
  rw [Metric.tendsto_atTop] at hSL hSU
  obtain ⟨N₁, hN₁⟩ := hSL (ε/4) (by linarith)
  obtain ⟨N₂, hN₂⟩ := hSU (ε/4) (by linarith)
  refine ⟨max 1 (max N₁ N₂), ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hN
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN1
  have h1 := hN₁ N (le_trans (le_trans (le_max_left _ _) (le_max_right 1 _)) hN)
  have h2 := hN₂ N (le_trans (le_trans (le_max_right _ _) (le_max_right 1 _)) hN)
  rw [Real.dist_eq, abs_lt] at h1 h2
  -- sandwich the orbit average
  have hlow : ∑ j ∈ Finset.range K,
      ((configCount x (Set.Ico ((j : ℝ) / K) (((j : ℝ) + 1) / K)) N : ℝ) / N) * g ((j:ℝ)/K)
      ≤ (∑ n ∈ Finset.range N, g (Int.fract (x n))) / N := by
    have heq : ∑ j ∈ Finset.range K,
        ((configCount x (Set.Ico ((j : ℝ) / K) (((j : ℝ) + 1) / K)) N : ℝ) / N) * g ((j:ℝ)/K)
        = (∑ j ∈ Finset.range K,
          (configCount x (Set.Ico ((j : ℝ) / K) (((j : ℝ) + 1) / K)) N : ℝ) * g ((j:ℝ)/K)) / N := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [heq]
    exact (div_le_div_iff_of_pos_right hNpos).mpr (sum_fiber_lower x hg hK1 N)
  have hhigh : (∑ n ∈ Finset.range N, g (Int.fract (x n))) / N
      ≤ ∑ j ∈ Finset.range K,
      ((configCount x (Set.Ico ((j : ℝ) / K) (((j : ℝ) + 1) / K)) N : ℝ) / N)
        * g (((j:ℝ)+1)/K) := by
    have heq : ∑ j ∈ Finset.range K,
        ((configCount x (Set.Ico ((j : ℝ) / K) (((j : ℝ) + 1) / K)) N : ℝ) / N)
          * g (((j:ℝ)+1)/K)
        = (∑ j ∈ Finset.range K,
          (configCount x (Set.Ico ((j : ℝ) / K) (((j : ℝ) + 1) / K)) N : ℝ)
            * g (((j:ℝ)+1)/K)) / N := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [heq]
    exact (div_le_div_iff_of_pos_right hNpos).mpr (sum_fiber_upper x hg hK1 N)
  rw [Real.dist_eq, abs_lt]
  constructor <;> [linarith; linarith]

end Monotone

variable {x : ℕ → ℝ} {f : ℝ → ℝ}

/-- Koksma-type reduction: for a function of bounded variation on `[0,1]`, the Cesàro
averages along an equidistributed sequence converge to the integral. -/
theorem tendsto_average_of_BV (hx : EquidistributedMod1 x)
    (hf : BoundedVariationOn f (Set.Icc (0:ℝ) 1)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (Int.fract (x n))) / N)
      atTop (𝓝 (∫ t in (0:ℝ)..1, f t)) := by
  obtain ⟨p, q, hp, hq, hpq⟩ :=
    hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  have hip : IntervalIntegrable p volume 0 1 := by
    apply MonotoneOn.intervalIntegrable
    rwa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  have hiq : IntervalIntegrable q volume 0 1 := by
    apply MonotoneOn.intervalIntegrable
    rwa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  have hsplit : (∫ t in (0:ℝ)..1, f t) = (∫ t in (0:ℝ)..1, p t) - ∫ t in (0:ℝ)..1, q t := by
    rw [← intervalIntegral.integral_sub hip hiq, hpq]
    simp [Pi.sub_apply]
  rw [hsplit]
  have hP := tendsto_average_of_monotoneOn hx hp
  have hQ := tendsto_average_of_monotoneOn hx hq
  refine (hP.sub hQ).congr ?_
  intro N
  rw [← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro n _
  rw [hpq]
  simp

/-- **Configuration count density from bounded variation.**  If the indicator function of a
configuration set `A` has bounded variation on `[0,1]`, then along any sequence that is
equidistributed mod `1` the configuration counts have a density, equal to the integral of the
indicator over `[0,1]`. -/
theorem configCount_density_of_BV (x : ℕ → ℝ) (hx : EquidistributedMod1 x) (A : Set ℝ)
    (hA : BoundedVariationOn (A.indicator (fun _ => (1:ℝ))) (Set.Icc (0:ℝ) 1)) :
    Tendsto (fun N : ℕ => (configCount x A N : ℝ) / N)
      atTop (𝓝 (∫ t in (0:ℝ)..1, A.indicator (fun _ => (1:ℝ)) t)) := by
  classical
  refine (tendsto_average_of_BV hx hA).congr ?_
  intro N
  congr 1
  rw [configCount]
  simp [Set.indicator_apply]

/-- Measure-theoretic form of the density statement: for a measurable configuration set `A`
whose indicator has bounded variation on `[0,1]`, the configuration counts along an
equidistributed sequence have density equal to the Lebesgue measure of `A ∩ (0,1]`. -/
theorem configCount_density_of_BV_measure (x : ℕ → ℝ) (hx : EquidistributedMod1 x) (A : Set ℝ)
    (hAm : MeasurableSet A)
    (hA : BoundedVariationOn (A.indicator (fun _ => (1:ℝ))) (Set.Icc (0:ℝ) 1)) :
    Tendsto (fun N : ℕ => (configCount x A N : ℝ) / N)
      atTop (𝓝 (volume.real (A ∩ Set.Ioc (0:ℝ) 1))) := by
  have hint : (∫ t in (0:ℝ)..1, A.indicator (fun _ => (1:ℝ)) t)
      = volume.real (A ∩ Set.Ioc (0:ℝ) 1) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      show (fun t => A.indicator (fun _ => (1:ℝ)) t) = A.indicator 1 from rfl,
      MeasureTheory.integral_indicator_one hAm, measureReal_restrict_apply hAm]
  simpa [hint] using configCount_density_of_BV x hx A hA

/-! ### Sanity check: the hypotheses are non-vacuous -/

lemma boundedVariationOn_of_monotoneOn_Icc01 {f : ℝ → ℝ}
    (hf : MonotoneOn f (Set.Icc (0:ℝ) 1)) : BoundedVariationOn f (Set.Icc (0:ℝ) 1) := by
  have h := hf.eVariationOn_le (a := 0) (b := 1) (by norm_num) (by norm_num)
  rw [Set.inter_eq_left.2 (by norm_num)] at h
  exact (h.trans_lt ENNReal.ofReal_lt_top).ne

lemma monotoneOn_indicator_Ici (c : ℝ) :
    MonotoneOn ((Set.Ici c).indicator (fun _ => (1:ℝ))) (Set.Icc (0:ℝ) 1) := by
  intro a _ b _ hab
  simp only [Set.indicator_apply, Set.mem_Ici]
  split_ifs with h1 h2 <;> try norm_num
  · linarith

/-- For a half-line configuration `A = [c, ∞)` with `0 < c ≤ 1` the density of the
configuration counts is `1 - c`. -/
theorem configCount_density_Ici (x : ℕ → ℝ) (hx : EquidistributedMod1 x) {c : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1) :
    Tendsto (fun N : ℕ => (configCount x (Set.Ici c) N : ℝ) / N) atTop (𝓝 (1 - c)) := by
  have hset : Set.Ici c ∩ Set.Ioc (0:ℝ) 1 = Set.Icc c 1 := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioc, Set.mem_Icc]
    constructor
    · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith, h2⟩
  have hvol : volume.real (Set.Ici c ∩ Set.Ioc (0:ℝ) 1) = 1 - c := by
    rw [hset]
    simp [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal, sub_nonneg.2 hc1]
  have := configCount_density_of_BV_measure x hx (Set.Ici c) measurableSet_Ici
    (boundedVariationOn_of_monotoneOn_Icc01 (monotoneOn_indicator_Ici c))
  rwa [hvol] at this

end Brockian.EquidistributionBVReduction

