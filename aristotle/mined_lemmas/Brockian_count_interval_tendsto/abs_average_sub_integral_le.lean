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
# Equidistribution Of BV Uniform
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Filter Finset MeasureTheory
open scoped Topology

namespace Brockian
namespace EquidistributionBVReduction

/-- A sequence `x : ℕ → ℝ` with values in `[0, 1)` is *uniformly distributed* if for every
`c ∈ [0, 1]` the proportion of the first `N` terms lying in `[0, c)` tends to `c`. -/

lemma abs_average_sub_integral_le (hx : UniformlyDistributed x) (hg : Monotone g)
    {k : ℕ} (hk : 0 < k) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      |(∑ n ∈ range N, g (x n)) / N - ∫ t in (0 : ℝ)..1, g t| ≤ (g 1 - g 0) / k + ε := by
  classical
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  set t : ℕ → ℝ := fun i => (i : ℝ) / k with htdef
  have ht0 : t 0 = 0 := by simp [htdef]
  have htk : t k = 1 := by
    simp only [htdef]
    field_simp
  have htsucc : ∀ i : ℕ, t (i + 1) = ((i : ℝ) + 1) / k := by
    intro i
    simp only [htdef]
    push_cast
    ring
  have htdiff : ∀ i : ℕ, t (i + 1) - t i = 1 / k := by
    intro i
    rw [htsucc i]
    simp only [htdef]
    ring
  have htmono : ∀ i : ℕ, t i ≤ t (i + 1) := by
    intro i
    have := htdiff i
    linarith [this, one_div_pos.2 hkR]
  have htnonneg : ∀ i : ℕ, 0 ≤ t i := by
    intro i; positivity
  set F : ℕ → ℕ → Finset ℕ := fun i N => (range N).filter (fun n => ⌊(k : ℝ) * x n⌋₊ = i)
    with hFdef
  have hmemF : ∀ (i N n : ℕ), n ∈ F i N ↔ (n ∈ range N ∧ t i ≤ x n ∧ x n < t (i + 1)) := by
    intro i N n
    simp only [hFdef, Finset.mem_filter]
    rw [floor_fiber_iff hk (hx.1 n).1, htsucc]
  have hFeq : ∀ (i N : ℕ),
      F i N = (range N).filter (fun n => t i ≤ x n ∧ x n < t (i + 1)) := by
    intro i N
    ext n
    rw [hmemF i N n, Finset.mem_filter]
  have hFcount : ∀ i < k, Tendsto (fun N : ℕ => ((F i N).card : ℝ) / N) atTop (𝓝 (1 / k)) := by
    intro i hi
    have hb : t (i + 1) ≤ 1 := by
      rw [htsucc, div_le_one hkR]
      have : (i : ℝ) + 1 ≤ k := by exact_mod_cast hi
      linarith
    have h := count_interval_tendsto hx (a := t i) (b := t (i + 1)) (htnonneg i) (htmono i) hb
    rw [htdiff i] at h
    simpa only [hFeq] using h
  have hsum_fiber : ∀ N : ℕ, ∑ i ∈ range k, ∑ n ∈ F i N, g (x n) = ∑ n ∈ range N, g (x n) := by
    intro N
    refine Finset.sum_fiberwise_of_maps_to ?_ _
    intro n _
    simp only [Finset.mem_range]
    have h1 : x n < 1 := (hx.1 n).2
    have h0 : 0 ≤ x n := (hx.1 n).1
    refine (Nat.floor_lt (by positivity)).2 ?_
    nlinarith
  have hupper : ∀ N : ℕ,
      (∑ n ∈ range N, g (x n)) ≤ ∑ i ∈ range k, ((F i N).card : ℝ) * g (t (i + 1)) := by
    intro N
    rw [← hsum_fiber N]
    refine Finset.sum_le_sum ?_
    intro i _
    have hb : ∀ n ∈ F i N, g (x n) ≤ g (t (i + 1)) := fun n hn =>
      hg ((hmemF i N n).1 hn).2.2.le
    calc ∑ n ∈ F i N, g (x n) ≤ (F i N).card • g (t (i + 1)) :=
          Finset.sum_le_card_nsmul _ _ _ hb
      _ = ((F i N).card : ℝ) * g (t (i + 1)) := by simp [nsmul_eq_mul]
  have hlower : ∀ N : ℕ,
      (∑ i ∈ range k, ((F i N).card : ℝ) * g (t i)) ≤ ∑ n ∈ range N, g (x n) := by
    intro N
    rw [← hsum_fiber N]
    refine Finset.sum_le_sum ?_
    intro i _
    have hb : ∀ n ∈ F i N, g (t i) ≤ g (x n) := fun n hn =>
      hg ((hmemF i N n).1 hn).2.1
    calc ((F i N).card : ℝ) * g (t i) = (F i N).card • g (t i) := by simp [nsmul_eq_mul]
      _ ≤ ∑ n ∈ F i N, g (x n) := Finset.card_nsmul_le_sum _ _ _ hb
  have hpart : ∑ i ∈ range k, (∫ s in (t i)..(t (i + 1)), g s) = ∫ s in (0 : ℝ)..1, g s := by
    have h := intervalIntegral.sum_integral_adjacent_intervals
      (f := g) (μ := MeasureTheory.volume) (a := t) (n := k)
      (fun i _ => hg.intervalIntegrable)
    rwa [ht0, htk] at h
  have hIle : (∫ s in (0 : ℝ)..1, g s) ≤ ∑ i ∈ range k, (1 / (k : ℝ)) * g (t (i + 1)) := by
    rw [← hpart]
    refine Finset.sum_le_sum ?_
    intro i _
    have h := integral_le_of_monotone hg (htmono i)
    rwa [htdiff i] at h
  have hIge : (∑ i ∈ range k, (1 / (k : ℝ)) * g (t i)) ≤ ∫ s in (0 : ℝ)..1, g s := by
    rw [← hpart]
    refine Finset.sum_le_sum ?_
    intro i _
    have h := le_integral_of_monotone hg (htmono i)
    rwa [htdiff i] at h
  have hUL : (∑ i ∈ range k, (1 / (k : ℝ)) * g (t (i + 1)))
      - (∑ i ∈ range k, (1 / (k : ℝ)) * g (t i)) = (g 1 - g 0) / k := by
    rw [← Finset.sum_sub_distrib]
    have hterm : ∀ i : ℕ, (1 / (k : ℝ)) * g (t (i + 1)) - (1 / (k : ℝ)) * g (t i)
        = (1 / (k : ℝ)) * (g (t (i + 1)) - g (t i)) := by intro i; ring
    simp_rw [hterm]
    rw [← Finset.mul_sum, Finset.sum_range_sub (fun i => g (t i)), ht0, htk]
    ring
  have hUlim : Tendsto (fun N : ℕ => ∑ i ∈ range k, (((F i N).card : ℝ) / N) * g (t (i + 1)))
      atTop (𝓝 (∑ i ∈ range k, (1 / (k : ℝ)) * g (t (i + 1)))) :=
    tendsto_finset_sum _ fun i hi => (hFcount i (Finset.mem_range.1 hi)).mul_const _
  have hLlim : Tendsto (fun N : ℕ => ∑ i ∈ range k, (((F i N).card : ℝ) / N) * g (t i))
      atTop (𝓝 (∑ i ∈ range k, (1 / (k : ℝ)) * g (t i))) :=
    tendsto_finset_sum _ fun i hi => (hFcount i (Finset.mem_range.1 hi)).mul_const _
  have hU' : ∀ᶠ N : ℕ in atTop,
      |(∑ i ∈ range k, (((F i N).card : ℝ) / N) * g (t (i + 1)))
        - ∑ i ∈ range k, (1 / (k : ℝ)) * g (t (i + 1))| ≤ ε := by
    rw [Metric.tendsto_atTop] at hUlim
    obtain ⟨N₁, h₁⟩ := hUlim ε hε
    filter_upwards [eventually_ge_atTop N₁] with N hN
    have := h₁ N hN
    rw [Real.dist_eq] at this
    linarith
  have hL' : ∀ᶠ N : ℕ in atTop,
      |(∑ i ∈ range k, (((F i N).card : ℝ) / N) * g (t i))
        - ∑ i ∈ range k, (1 / (k : ℝ)) * g (t i)| ≤ ε := by
    rw [Metric.tendsto_atTop] at hLlim
    obtain ⟨N₁, h₁⟩ := hLlim ε hε
    filter_upwards [eventually_ge_atTop N₁] with N hN
    have := h₁ N hN
    rw [Real.dist_eq] at this
    linarith
  filter_upwards [eventually_gt_atTop 0, hU', hL'] with N hN hUN hLN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hSU : (∑ n ∈ range N, g (x n)) / N
      ≤ ∑ i ∈ range k, (((F i N).card : ℝ) / N) * g (t (i + 1)) := by
    have hrw : (∑ i ∈ range k, (((F i N).card : ℝ) / N) * g (t (i + 1)))
        = (∑ i ∈ range k, ((F i N).card : ℝ) * g (t (i + 1))) / N := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hrw]
    exact (div_le_div_iff_of_pos_right hNR).mpr (hupper N)
  have hSL : (∑ i ∈ range k, (((F i N).card : ℝ) / N) * g (t i))
      ≤ (∑ n ∈ range N, g (x n)) / N := by
    have hrw : (∑ i ∈ range k, (((F i N).card : ℝ) / N) * g (t i))
        = (∑ i ∈ range k, ((F i N).card : ℝ) * g (t i)) / N := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hrw]
    exact (div_le_div_iff_of_pos_right hNR).mpr (hlower N)
  rw [abs_le] at hUN hLN ⊢
  constructor
  · linarith [hUN.1, hUN.2, hLN.1, hLN.2, hIle, hIge, hUL, hSU, hSL]
  · linarith [hUN.1, hUN.2, hLN.1, hLN.2, hIle, hIge, hUL, hSU, hSL]

/-- Equidistribution for monotone functions. -/
