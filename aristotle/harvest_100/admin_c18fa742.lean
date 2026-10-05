import Mathlib
import RequestProject.Brockian.EquidistributionBVReduction

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
# Equidistribution Of BV Uniform
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Finset Set
open scoped Topology BigOperators Classical

set_option maxHeartbeats 1000000

namespace Brockian
namespace EquidistributionBVReduction

/-- `countIn x a b N` is the number of indices `n < N` with `x n ∈ [a, b)`. -/
noncomputable def countIn (x : ℕ → ℝ) (a b : ℝ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => x n ∈ Set.Ico a b)).card

/-- A sequence `x` with values in `[0,1)` is *uniformly distributed* if, for every
subinterval `[a,b) ⊆ [0,1]`, the proportion of the first `N` terms lying in `[a,b)`
tends to its length `b - a`. -/
def UniformlyDistributed (x : ℕ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
    Tendsto (fun N : ℕ => (countIn x a b N : ℝ) / (N : ℝ)) atTop (𝓝 (b - a))

variable {x : ℕ → ℝ} {g : ℝ → ℝ} {k : ℕ}

/-- The fibers of `n ↦ ⌊k * x n⌋₊` are exactly the index sets of the intervals
`[j/k, (j+1)/k)`. -/
lemma fiber_eq_filter_Ico (hx : ∀ n, 0 ≤ x n) (hk : 0 < k) (j N : ℕ) :
    ((Finset.range N).filter (fun n => ⌊(k : ℝ) * x n⌋₊ = j)) =
      ((Finset.range N).filter (fun n => x n ∈ Set.Ico ((j : ℝ) / k) (((j : ℝ) + 1) / k))) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  refine Finset.filter_congr ?_
  intro n _
  have h0 : 0 ≤ (k : ℝ) * x n := mul_nonneg hk'.le (hx n)
  rw [Nat.floor_eq_iff h0, Set.mem_Ico, div_le_iff₀ hk', lt_div_iff₀ hk']
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

/-- Every index `n < N` lies in one of the `k` fibers. -/
lemma floor_mem_range (hx : ∀ n, x n ∈ Set.Ico (0 : ℝ) 1) (hk : 0 < k) (N : ℕ) :
    ∀ n ∈ Finset.range N, ⌊(k : ℝ) * x n⌋₊ ∈ Finset.range k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  intro n _
  simp only [Finset.mem_range]
  have h1 : (k : ℝ) * x n < k := by nlinarith [(hx n).1, (hx n).2]
  exact_mod_cast (Nat.floor_lt (mul_nonneg hk'.le (hx n).1)).2 (by exact_mod_cast h1)

/-- Upper bound of the sum of a monotone function along the sequence by the upper Darboux
sum weighted with the counting function. -/
lemma sum_le_upper (hx : ∀ n, x n ∈ Set.Ico (0 : ℝ) 1) (hg : MonotoneOn g (Set.Icc 0 1))
    (hk : 0 < k) (N : ℕ) :
    ∑ n ∈ Finset.range N, g (x n) ≤
      ∑ j ∈ Finset.range k,
        g (((j : ℝ) + 1) / k) * (countIn x ((j : ℝ) / k) (((j : ℝ) + 1) / k) N : ℝ) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [← Finset.sum_fiberwise_of_maps_to (floor_mem_range hx hk N) (fun n => g (x n))]
  refine Finset.sum_le_sum ?_
  intro j hj
  have hjk : (j : ℝ) + 1 ≤ k := by exact_mod_cast Finset.mem_range.1 hj
  have hmem1 : ((j : ℝ) + 1) / k ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by positivity, by rw [div_le_one hk']; exact hjk⟩
  rw [fiber_eq_filter_Ico (fun n => (hx n).1) hk j N]
  have hb : ∀ n ∈ ((Finset.range N).filter
      (fun n => x n ∈ Set.Ico ((j : ℝ) / k) (((j : ℝ) + 1) / k))),
      g (x n) ≤ g (((j : ℝ) + 1) / k) := by
    intro n hn
    exact hg ⟨(hx n).1, (hx n).2.le⟩ hmem1 (Finset.mem_filter.1 hn).2.2.le
  calc ∑ n ∈ _, g (x n) ≤ _ • g (((j : ℝ) + 1) / k) := Finset.sum_le_card_nsmul _ _ _ hb
    _ = g (((j : ℝ) + 1) / k) * (countIn x ((j : ℝ) / k) (((j : ℝ) + 1) / k) N : ℝ) := by
        rw [nsmul_eq_mul, countIn]; ring

/-- Lower bound of the sum of a monotone function along the sequence by the lower Darboux
sum weighted with the counting function. -/
lemma lower_le_sum (hx : ∀ n, x n ∈ Set.Ico (0 : ℝ) 1) (hg : MonotoneOn g (Set.Icc 0 1))
    (hk : 0 < k) (N : ℕ) :
    ∑ j ∈ Finset.range k,
        g ((j : ℝ) / k) * (countIn x ((j : ℝ) / k) (((j : ℝ) + 1) / k) N : ℝ) ≤
      ∑ n ∈ Finset.range N, g (x n) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [← Finset.sum_fiberwise_of_maps_to (floor_mem_range hx hk N) (fun n => g (x n))]
  refine Finset.sum_le_sum ?_
  intro j hj
  have hjk : (j : ℝ) + 1 ≤ k := by exact_mod_cast Finset.mem_range.1 hj
  have hmem0 : (j : ℝ) / k ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by positivity, by rw [div_le_one hk']; linarith⟩
  rw [fiber_eq_filter_Ico (fun n => (hx n).1) hk j N]
  have hb : ∀ n ∈ ((Finset.range N).filter
      (fun n => x n ∈ Set.Ico ((j : ℝ) / k) (((j : ℝ) + 1) / k))),
      g ((j : ℝ) / k) ≤ g (x n) := by
    intro n hn
    exact hg hmem0 ⟨(hx n).1, (hx n).2.le⟩ (Finset.mem_filter.1 hn).2.1
  calc g ((j : ℝ) / k) * (countIn x ((j : ℝ) / k) (((j : ℝ) + 1) / k) N : ℝ)
      = _ • g ((j : ℝ) / k) := by rw [nsmul_eq_mul, countIn]; ring
    _ ≤ ∑ n ∈ _, g (x n) := Finset.card_nsmul_le_sum _ _ _ hb

/-- The normalized weighted counting sums converge to the corresponding Darboux sums. -/
lemma tendsto_weighted_count (hud : UniformlyDistributed x) (hk : 0 < k) (c : ℕ → ℝ) :
    Tendsto (fun N : ℕ => ∑ j ∈ Finset.range k,
        c j * ((countIn x ((j : ℝ) / k) (((j : ℝ) + 1) / k) N : ℝ) / (N : ℝ))) atTop
      (𝓝 (∑ j ∈ Finset.range k, c j * (1 / (k : ℝ)))) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  refine tendsto_finset_sum _ ?_
  intro j hj
  have hj' : (j : ℝ) + 1 ≤ k := by exact_mod_cast Finset.mem_range.1 hj
  have h1 : (0 : ℝ) ≤ (j : ℝ) / k := by positivity
  have h2 : (j : ℝ) / k ≤ ((j : ℝ) + 1) / k := by
    gcongr
    linarith
  have h3 : ((j : ℝ) + 1) / k ≤ 1 := by rw [div_le_one hk']; exact hj'
  have hlim := (hud ((j : ℝ) / k) (((j : ℝ) + 1) / k) h1 h2 h3).const_mul (c j)
  have heq : ((j : ℝ) + 1) / k - (j : ℝ) / k = 1 / (k : ℝ) := by field_simp; ring
  rw [heq] at hlim
  exact hlim

/-- The integral is bounded above by the upper Darboux sum. -/
lemma integral_le_upper (hg : MonotoneOn g (Set.Icc 0 1)) (hk : 0 < k) :
    (∫ t in (0 : ℝ)..1, g t) ≤ ∑ j ∈ Finset.range k, g (((j : ℝ) + 1) / k) * (1 / (k : ℝ)) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  set a : ℕ → ℝ := fun j => (j : ℝ) / k with ha
  have hmemIcc : ∀ j ≤ k, a j ∈ Set.Icc (0 : ℝ) 1 := by
    intro j hj
    refine ⟨by positivity, ?_⟩
    show (j : ℝ) / k ≤ 1
    rw [div_le_one hk']
    exact_mod_cast hj
  have hle : ∀ j, a j ≤ a (j + 1) := by
    intro j
    show (j : ℝ) / k ≤ ((j + 1 : ℕ) : ℝ) / k
    gcongr
    linarith
  have hsub : ∀ j < k, Set.Icc (a j) (a (j + 1)) ⊆ Set.Icc (0 : ℝ) 1 := by
    intro j hj t ht
    exact ⟨le_trans (hmemIcc j hj.le).1 ht.1, le_trans ht.2 (hmemIcc (j + 1) hj).2⟩
  have hint : ∀ j < k, IntervalIntegrable g MeasureTheory.volume (a j) (a (j + 1)) := by
    intro j hj
    apply MonotoneOn.intervalIntegrable
    apply hg.mono
    rw [Set.uIcc_of_le (hle j)]
    exact hsub j hj
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals hint
  have h0 : a 0 = 0 := by show ((0 : ℕ) : ℝ) / k = 0; simp
  have h1 : a k = 1 := by show (k : ℝ) / k = 1; field_simp
  rw [h0, h1] at hsplit
  rw [← hsplit]
  refine Finset.sum_le_sum ?_
  intro j hj
  have hj' : j < k := Finset.mem_range.1 hj
  have hmono : ∀ t ∈ Set.Icc (a j) (a (j + 1)), g t ≤ g (a (j + 1)) := fun t ht =>
    hg (hsub j hj' ht) (hmemIcc (j + 1) hj') ht.2
  have key := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) (hle j) (hint j hj')
    intervalIntegrable_const hmono
  rw [intervalIntegral.integral_const] at key
  have hdiff : a (j + 1) - a j = 1 / (k : ℝ) := by
    show ((j + 1 : ℕ) : ℝ) / k - (j : ℝ) / k = 1 / k
    push_cast; ring
  have hcast : a (j + 1) = ((j : ℝ) + 1) / k := by
    show ((j + 1 : ℕ) : ℝ) / k = _
    push_cast; ring
  rw [hdiff, smul_eq_mul, hcast] at key
  rw [hcast]
  linarith

/-- The integral is bounded below by the lower Darboux sum. -/
lemma lower_le_integral (hg : MonotoneOn g (Set.Icc 0 1)) (hk : 0 < k) :
    ∑ j ∈ Finset.range k, g ((j : ℝ) / k) * (1 / (k : ℝ)) ≤ (∫ t in (0 : ℝ)..1, g t) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  set a : ℕ → ℝ := fun j => (j : ℝ) / k with ha
  have hmemIcc : ∀ j ≤ k, a j ∈ Set.Icc (0 : ℝ) 1 := by
    intro j hj
    refine ⟨by positivity, ?_⟩
    show (j : ℝ) / k ≤ 1
    rw [div_le_one hk']
    exact_mod_cast hj
  have hle : ∀ j, a j ≤ a (j + 1) := by
    intro j
    show (j : ℝ) / k ≤ ((j + 1 : ℕ) : ℝ) / k
    gcongr
    linarith
  have hsub : ∀ j < k, Set.Icc (a j) (a (j + 1)) ⊆ Set.Icc (0 : ℝ) 1 := by
    intro j hj t ht
    exact ⟨le_trans (hmemIcc j hj.le).1 ht.1, le_trans ht.2 (hmemIcc (j + 1) hj).2⟩
  have hint : ∀ j < k, IntervalIntegrable g MeasureTheory.volume (a j) (a (j + 1)) := by
    intro j hj
    apply MonotoneOn.intervalIntegrable
    apply hg.mono
    rw [Set.uIcc_of_le (hle j)]
    exact hsub j hj
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals hint
  have h0 : a 0 = 0 := by show ((0 : ℕ) : ℝ) / k = 0; simp
  have h1 : a k = 1 := by show (k : ℝ) / k = 1; field_simp
  rw [h0, h1] at hsplit
  rw [← hsplit]
  refine Finset.sum_le_sum ?_
  intro j hj
  have hj' : j < k := Finset.mem_range.1 hj
  have hmono : ∀ t ∈ Set.Icc (a j) (a (j + 1)), g (a j) ≤ g t := fun t ht =>
    hg (hmemIcc j hj'.le) (hsub j hj' ht) ht.1
  have key := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) (hle j)
    intervalIntegrable_const (hint j hj') hmono
  rw [intervalIntegral.integral_const] at key
  have hdiff : a (j + 1) - a j = 1 / (k : ℝ) := by
    show ((j + 1 : ℕ) : ℝ) / k - (j : ℝ) / k = 1 / k
    push_cast; ring
  have hcast : a j = (j : ℝ) / k := rfl
  rw [hdiff, smul_eq_mul, hcast] at key
  linarith

/-- The gap between the upper and the lower Darboux sum is `(g 1 - g 0)/k`. -/
lemma upper_sub_lower (hk : 0 < k) :
    (∑ j ∈ Finset.range k, g (((j : ℝ) + 1) / k) * (1 / (k : ℝ))) -
        (∑ j ∈ Finset.range k, g ((j : ℝ) / k) * (1 / (k : ℝ))) = (g 1 - g 0) / k := by
  have h := Finset.sum_range_sub (f := fun j : ℕ => g ((j : ℝ) / k) * (1 / (k : ℝ))) (n := k)
  rw [← Finset.sum_sub_distrib]
  have hcongr : ∀ j ∈ Finset.range k,
      g (((j : ℝ) + 1) / k) * (1 / (k : ℝ)) - g ((j : ℝ) / k) * (1 / (k : ℝ))
        = (fun j : ℕ => g ((j : ℝ) / k) * (1 / (k : ℝ))) (j + 1)
          - (fun j : ℕ => g ((j : ℝ) / k) * (1 / (k : ℝ))) j := by
    intro j _
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl hcongr, h]
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  rw [Nat.cast_zero, zero_div, div_self hk']
  ring

/-- Koksma's theorem for monotone functions: along a uniformly distributed sequence the
Cesàro averages of a monotone function converge to its integral. -/
lemma tendsto_average_of_monotoneOn (hx : ∀ n, x n ∈ Set.Ico (0 : ℝ) 1)
    (hud : UniformlyDistributed x) (hg : MonotoneOn g (Set.Icc 0 1)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, g (x n)) / (N : ℝ)) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, g t)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hD : 0 ≤ g 1 - g 0 := by
    have := hg (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
      (by norm_num : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1) (by norm_num)
    linarith
  obtain ⟨k, hmk⟩ := exists_nat_gt (2 * (g 1 - g 0) / ε + 1)
  have hnn : 0 ≤ 2 * (g 1 - g 0) / ε := by positivity
  have hk' : (1 : ℝ) < k := by linarith
  have hk : 0 < k := by exact_mod_cast lt_trans zero_lt_one hk'
  have hkR : (0 : ℝ) < k := by linarith
  have hgap : (g 1 - g 0) / (k : ℝ) < ε / 2 := by
    have h1 : 2 * (g 1 - g 0) < (k : ℝ) * ε := (div_lt_iff₀ hε).1 (by linarith)
    rw [div_lt_div_iff₀ hkR two_pos]
    linarith
  have hLI := lower_le_integral hg hk
  have hIU := integral_le_upper hg hk
  have hUL := upper_sub_lower (g := g) hk
  have hlow := tendsto_weighted_count hud hk (fun j => g ((j : ℝ) / k))
  have hupp := tendsto_weighted_count hud hk (fun j => g (((j : ℝ) + 1) / k))
  simp only at hlow hupp
  rw [Metric.tendsto_atTop] at hlow hupp
  obtain ⟨N1, hN1⟩ := hlow (ε / 4) (by linarith)
  obtain ⟨N2, hN2⟩ := hupp (ε / 4) (by linarith)
  refine ⟨max (max N1 N2) 1, ?_⟩
  intro N hN
  have hN1' := hN1 N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN)
  have hN2' := hN2 N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN)
  have hNpos : (0 : ℝ) < N := by
    have h1 : 1 ≤ N := le_trans (le_max_right _ _) hN
    exact_mod_cast h1
  rw [Real.dist_eq, abs_lt] at hN1' hN2'
  have hlowdiv : ∑ j ∈ Finset.range k,
      g ((j : ℝ) / k) * ((countIn x ((j : ℝ) / k) (((j : ℝ) + 1) / k) N : ℝ) / (N : ℝ))
      = (∑ j ∈ Finset.range k,
          g ((j : ℝ) / k) * (countIn x ((j : ℝ) / k) (((j : ℝ) + 1) / k) N : ℝ)) / (N : ℝ) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have huppdiv : ∑ j ∈ Finset.range k,
      g (((j : ℝ) + 1) / k) * ((countIn x ((j : ℝ) / k) (((j : ℝ) + 1) / k) N : ℝ) / (N : ℝ))
      = (∑ j ∈ Finset.range k,
          g (((j : ℝ) + 1) / k)
            * (countIn x ((j : ℝ) / k) (((j : ℝ) + 1) / k) N : ℝ)) / (N : ℝ) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hlowS : ∑ j ∈ Finset.range k,
      g ((j : ℝ) / k) * ((countIn x ((j : ℝ) / k) (((j : ℝ) + 1) / k) N : ℝ) / (N : ℝ))
      ≤ (∑ n ∈ Finset.range N, g (x n)) / (N : ℝ) := by
    rw [hlowdiv]
    exact (div_le_div_iff_of_pos_right hNpos).mpr (lower_le_sum hx hg hk N)
  have hSupp : (∑ n ∈ Finset.range N, g (x n)) / (N : ℝ)
      ≤ ∑ j ∈ Finset.range k,
        g (((j : ℝ) + 1) / k) * ((countIn x ((j : ℝ) / k) (((j : ℝ) + 1) / k) N : ℝ) / (N : ℝ)) := by
    rw [huppdiv]
    exact (div_le_div_iff_of_pos_right hNpos).mpr (sum_le_upper hx hg hk N)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- **Koksma's equidistribution theorem for functions of bounded variation.**
If `x` is a sequence in `[0,1)` that is uniformly distributed and `f` has bounded variation
on `[0,1]`, then the Cesàro averages of `f` along `x` converge to `∫₀¹ f`. -/
theorem equidistribution_of_BV_uniform (x : ℕ → ℝ) (f : ℝ → ℝ)
    (hx : ∀ n, x n ∈ Set.Ico (0 : ℝ) 1) (hud : UniformlyDistributed x)
    (hf : BoundedVariationOn f (Set.Icc (0 : ℝ) 1)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (x n)) / (N : ℝ)) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, f t)) := by
  obtain ⟨p, q, hp, hq, hpq⟩ :=
    hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  have hpu : MonotoneOn p (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le zero_le_one]; exact hp
  have hqu : MonotoneOn q (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le zero_le_one]; exact hq
  have hpi : IntervalIntegrable p MeasureTheory.volume 0 1 := hpu.intervalIntegrable
  have hqi : IntervalIntegrable q MeasureTheory.volume 0 1 := hqu.intervalIntegrable
  have hInt : (∫ t in (0 : ℝ)..1, f t)
      = (∫ t in (0 : ℝ)..1, p t) - (∫ t in (0 : ℝ)..1, q t) := by
    rw [hpq]
    simp only [Pi.sub_apply]
    exact intervalIntegral.integral_sub hpi hqi
  have hsum : ∀ N : ℕ, (∑ n ∈ Finset.range N, f (x n)) / (N : ℝ)
      = (∑ n ∈ Finset.range N, p (x n)) / (N : ℝ)
        - (∑ n ∈ Finset.range N, q (x n)) / (N : ℝ) := by
    intro N
    rw [hpq]
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, sub_div]
  rw [hInt]
  simp only [hsum]
  exact (tendsto_average_of_monotoneOn hx hud hp).sub (tendsto_average_of_monotoneOn hx hud hq)

end EquidistributionBVReduction
end Brockian

