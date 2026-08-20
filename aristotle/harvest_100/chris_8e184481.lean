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
# Equidistribution Of BV Uniform
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Finset MeasureTheory
open scoped Topology BigOperators Classical

namespace Brockian
namespace EquidistributionBVReduction

/-- The number of indices `n < N` for which the fractional part of `x n` lies in `[a, b)`. -/
noncomputable def countIn (x : ℕ → ℝ) (a b : ℝ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => Int.fract (x n) ∈ Set.Ico a b)).card

/-- A sequence of reals is *uniformly distributed mod 1* if, for every subinterval `[a, b)` of
`[0, 1]`, the proportion of the first `N` terms whose fractional part lies in `[a, b)` tends to
the length `b - a` of the interval. -/
def UniformlyDistributedMod1 (x : ℕ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
    Tendsto (fun N : ℕ => (countIn x a b N : ℝ) / N) atTop (𝓝 (b - a))

section Helpers

variable {x : ℕ → ℝ} {g : ℝ → ℝ}

/-- Membership in the `i`-th dyadic-type subinterval of `[0,1)` is detected by the floor of
`K * y`. -/
lemma floor_eq_iff_mem_Ico {K : ℕ} (hK : 0 < K) {y : ℝ} (hy : 0 ≤ y) (i : ℕ) :
    ⌊(K : ℝ) * y⌋₊ = i ↔ y ∈ Set.Ico ((i : ℝ) / K) (((i : ℝ) + 1) / K) := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  rw [Nat.floor_eq_iff (by positivity)]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(div_le_iff₀ hKpos).2 (by linarith [h1]), (lt_div_iff₀ hKpos).2 (by linarith [h2])⟩
  · rintro ⟨h1, h2⟩
    have h1' := (div_le_iff₀ hKpos).1 h1
    have h2' := (lt_div_iff₀ hKpos).1 h2
    constructor <;> nlinarith

/-- The fibers of `n ↦ ⌊K * fract (x n)⌋₊` decompose a sum over `range N` into sums over the
subintervals `[i/K, (i+1)/K)`. -/
lemma sum_eq_sum_fibers (x : ℕ → ℝ) (g : ℝ → ℝ) {K : ℕ} (hK : 0 < K) (N : ℕ) :
    ∑ n ∈ Finset.range N, g (Int.fract (x n)) =
      ∑ i ∈ Finset.range K,
        ∑ n ∈ (Finset.range N).filter
          (fun n => Int.fract (x n) ∈ Set.Ico ((i : ℝ) / K) (((i : ℝ) + 1) / K)),
          g (Int.fract (x n)) := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hmaps : ∀ n ∈ Finset.range N, ⌊(K : ℝ) * Int.fract (x n)⌋₊ ∈ Finset.range K := by
    intro n _
    refine Finset.mem_range.2 ?_
    have h1 : Int.fract (x n) < 1 := Int.fract_lt_one _
    have : (K : ℝ) * Int.fract (x n) < (K : ℝ) := by nlinarith
    exact Nat.floor_lt' (by omega) |>.2 (by simpa using this)
  have := Finset.sum_fiberwise_of_maps_to hmaps (fun n => g (Int.fract (x n)))
  rw [← this]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  refine Finset.filter_congr (fun n _ => ?_)
  simpa using floor_eq_iff_mem_Ico hK (Int.fract_nonneg (x n)) i

/-- Lower step-function bound for the partial sums. -/
lemma sum_lower_bound (hg : Monotone g) (x : ℕ → ℝ) {K : ℕ} (hK : 0 < K) (N : ℕ) :
    ∑ i ∈ Finset.range K,
        (countIn x ((i : ℝ) / K) (((i : ℝ) + 1) / K) N : ℝ) * g ((i : ℝ) / K) ≤
      ∑ n ∈ Finset.range N, g (Int.fract (x n)) := by
  rw [sum_eq_sum_fibers x g hK N]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have h := Finset.card_nsmul_le_sum
    ((Finset.range N).filter
      (fun n => Int.fract (x n) ∈ Set.Ico ((i : ℝ) / K) (((i : ℝ) + 1) / K)))
    (fun n => g (Int.fract (x n))) (g ((i : ℝ) / K)) ?_
  · simpa [countIn, nsmul_eq_mul, mul_comm] using h
  · intro n hn
    have := (Finset.mem_filter.1 hn).2
    exact hg this.1

/-- Upper step-function bound for the partial sums. -/
lemma sum_upper_bound (hg : Monotone g) (x : ℕ → ℝ) {K : ℕ} (hK : 0 < K) (N : ℕ) :
    ∑ n ∈ Finset.range N, g (Int.fract (x n)) ≤
      ∑ i ∈ Finset.range K,
        (countIn x ((i : ℝ) / K) (((i : ℝ) + 1) / K) N : ℝ) * g (((i : ℝ) + 1) / K) := by
  rw [sum_eq_sum_fibers x g hK N]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have h := Finset.sum_le_card_nsmul
    ((Finset.range N).filter
      (fun n => Int.fract (x n) ∈ Set.Ico ((i : ℝ) / K) (((i : ℝ) + 1) / K)))
    (fun n => g (Int.fract (x n))) (g (((i : ℝ) + 1) / K)) ?_
  · simpa [countIn, nsmul_eq_mul, mul_comm] using h
  · intro n hn
    have := (Finset.mem_filter.1 hn).2
    exact hg (le_of_lt this.2)

/-- The lower Riemann sum of a monotone function underestimates its integral. -/
lemma lower_sum_le_integral (hg : Monotone g) {K : ℕ} (hK : 0 < K) :
    ∑ i ∈ Finset.range K, g ((i : ℝ) / K) / K ≤ ∫ t in (0:ℝ)..1, g t := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hsum : ∑ i ∈ Finset.range K, ∫ t in ((i : ℝ) / K)..(((i : ℝ) + 1) / K), g t =
      ∫ t in (0:ℝ)..1, g t := by
    have := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun i : ℕ => (i : ℝ) / K) (f := g) (μ := volume) (n := K)
      (fun k _ => hg.intervalIntegrable)
    simpa [Nat.cast_add, Nat.cast_one, div_self (ne_of_gt hKpos)] using this
  rw [← hsum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have hle : (i : ℝ) / K ≤ ((i : ℝ) + 1) / K := by
    rw [div_le_div_iff_of_pos_right hKpos]; linarith
  have hmono : ∫ t in ((i : ℝ) / K)..(((i : ℝ) + 1) / K), g ((i : ℝ) / K) ≤
      ∫ t in ((i : ℝ) / K)..(((i : ℝ) + 1) / K), g t :=
    intervalIntegral.integral_mono_on hle intervalIntegrable_const
      hg.intervalIntegrable (fun t ht => hg ht.1)
  calc g ((i : ℝ) / K) / K
      = ∫ _t in ((i : ℝ) / K)..(((i : ℝ) + 1) / K), g ((i : ℝ) / K) := by
        rw [intervalIntegral.integral_const, smul_eq_mul,
          show ((i : ℝ) + 1) / K - (i : ℝ) / K = 1 / K by rw [div_sub_div_same]; norm_num]
        ring
    _ ≤ _ := hmono

/-- The upper Riemann sum of a monotone function overestimates its integral. -/
lemma integral_le_upper_sum (hg : Monotone g) {K : ℕ} (hK : 0 < K) :
    (∫ t in (0:ℝ)..1, g t) ≤ ∑ i ∈ Finset.range K, g (((i : ℝ) + 1) / K) / K := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hsum : ∑ i ∈ Finset.range K, ∫ t in ((i : ℝ) / K)..(((i : ℝ) + 1) / K), g t =
      ∫ t in (0:ℝ)..1, g t := by
    have := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun i : ℕ => (i : ℝ) / K) (f := g) (μ := volume) (n := K)
      (fun k _ => hg.intervalIntegrable)
    simpa [Nat.cast_add, Nat.cast_one, div_self (ne_of_gt hKpos)] using this
  rw [← hsum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have hle : (i : ℝ) / K ≤ ((i : ℝ) + 1) / K := by
    rw [div_le_div_iff_of_pos_right hKpos]; linarith
  have hmono : ∫ t in ((i : ℝ) / K)..(((i : ℝ) + 1) / K), g t ≤
      ∫ _t in ((i : ℝ) / K)..(((i : ℝ) + 1) / K), g (((i : ℝ) + 1) / K) :=
    intervalIntegral.integral_mono_on hle hg.intervalIntegrable intervalIntegrable_const
      (fun t ht => hg ht.2)
  calc ∫ t in ((i : ℝ) / K)..(((i : ℝ) + 1) / K), g t
      ≤ ∫ _t in ((i : ℝ) / K)..(((i : ℝ) + 1) / K), g (((i : ℝ) + 1) / K) := hmono
    _ = g (((i : ℝ) + 1) / K) / K := by
        rw [intervalIntegral.integral_const, smul_eq_mul,
          show ((i : ℝ) + 1) / K - (i : ℝ) / K = 1 / K by rw [div_sub_div_same]; norm_num]
        ring

end Helpers

/-- **Weyl's theorem for monotone test functions**: if `x` is uniformly distributed mod 1 then
the averages of a monotone function along `fract (x n)` converge to its integral over `[0,1]`. -/
theorem tendsto_average_of_monotone {x : ℕ → ℝ} (hx : UniformlyDistributedMod1 x)
    {g : ℝ → ℝ} (hg : Monotone g) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, g (Int.fract (x n))) / N) atTop
      (𝓝 (∫ t in (0:ℝ)..1, g t)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set I : ℝ := ∫ t in (0:ℝ)..1, g t
  obtain ⟨K0, hK0⟩ := exists_nat_gt (4 * (g 1 - g 0) / ε)
  obtain ⟨K, hK, hKgt⟩ : ∃ K : ℕ, 0 < K ∧ 4 * (g 1 - g 0) / ε < K :=
    ⟨K0 + 1, Nat.succ_pos _, lt_of_lt_of_le hK0 (by exact_mod_cast Nat.le_succ K0)⟩
  have hKpos : (0:ℝ) < K := by exact_mod_cast hK
  have hDK : (g 1 - g 0) / K < ε / 4 := by
    have h1 : 4 * (g 1 - g 0) < K * ε := (div_lt_iff₀ hε).1 hKgt
    rw [div_lt_iff₀ hKpos]
    linarith
  -- the normalized counting functions converge to `1 / K`
  have hcount : ∀ i ∈ Finset.range K,
      Tendsto (fun N : ℕ => (countIn x ((i:ℝ)/K) (((i:ℝ)+1)/K) N : ℝ) / N) atTop
        (𝓝 (1/(K:ℝ))) := by
    intro i hi
    have hiK : (i : ℝ) + 1 ≤ K := by
      have h := Finset.mem_range.1 hi
      exact_mod_cast Nat.succ_le_of_lt h
    have h := hx ((i:ℝ)/K) (((i:ℝ)+1)/K) (by positivity)
      (by rw [div_le_div_iff_of_pos_right hKpos]; linarith)
      (by rw [div_le_one hKpos]; linarith)
    have heq : ((i:ℝ)+1)/K - (i:ℝ)/K = 1/K := by rw [div_sub_div_same]; norm_num
    rwa [heq] at h
  set L : ℝ := ∑ i ∈ Finset.range K, (1/(K:ℝ)) * g ((i:ℝ)/K) with hLdef
  set U : ℝ := ∑ i ∈ Finset.range K, (1/(K:ℝ)) * g (((i:ℝ)+1)/K) with hUdef
  have hLN : Tendsto (fun N : ℕ =>
      ∑ i ∈ Finset.range K,
        ((countIn x ((i:ℝ)/K) (((i:ℝ)+1)/K) N : ℝ)/N) * g ((i:ℝ)/K)) atTop (𝓝 L) :=
    tendsto_finset_sum _ (fun i hi => (hcount i hi).mul_const _)
  have hUN : Tendsto (fun N : ℕ =>
      ∑ i ∈ Finset.range K,
        ((countIn x ((i:ℝ)/K) (((i:ℝ)+1)/K) N : ℝ)/N) * g (((i:ℝ)+1)/K)) atTop (𝓝 U) :=
    tendsto_finset_sum _ (fun i hi => (hcount i hi).mul_const _)
  -- the two Riemann sums bracket the integral, and differ by `(g 1 - g 0) / K`
  have hLI : L ≤ I := by
    calc L = ∑ i ∈ Finset.range K, g ((i:ℝ)/K) / K :=
          Finset.sum_congr rfl (fun i _ => by ring)
      _ ≤ I := lower_sum_le_integral hg hK
  have hIU : I ≤ U := by
    calc I ≤ ∑ i ∈ Finset.range K, g (((i:ℝ)+1)/K) / K := integral_le_upper_sum hg hK
      _ = U := Finset.sum_congr rfl (fun i _ => by ring)
  have hUsubL : U - L = (g 1 - g 0) / K := by
    have hFsum : ∑ i ∈ Finset.range K,
        (g (((i + 1 : ℕ) : ℝ)/(K:ℝ)) - g ((i : ℝ)/K)) = g 1 - g 0 := by
      have h := Finset.sum_range_sub (fun i : ℕ => g ((i : ℝ)/K)) K
      simpa [div_self (ne_of_gt hKpos)] using h
    have hstep : U - L = ∑ i ∈ Finset.range K,
        (1/(K:ℝ)) * (g (((i + 1 : ℕ) : ℝ)/(K:ℝ)) - g ((i : ℝ)/K)) := by
      rw [hUdef, hLdef, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      push_cast
      ring
    rw [hstep, ← Finset.mul_sum, hFsum]
    ring
  -- combine everything
  obtain ⟨N1, hN1⟩ := (Metric.tendsto_atTop.1 hLN) (ε/4) (by linarith)
  obtain ⟨N2, hN2⟩ := (Metric.tendsto_atTop.1 hUN) (ε/4) (by linarith)
  refine ⟨max (max N1 N2) 1, fun N hN => ?_⟩
  have hNpos : 0 < N := lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right _ 1) hN)
  have hNR : (0:ℝ) < N := by exact_mod_cast hNpos
  have hb1 := hN1 N (le_trans (le_trans (le_max_left N1 N2) (le_max_left _ 1)) hN)
  have hb2 := hN2 N (le_trans (le_trans (le_max_right N1 N2) (le_max_left _ 1)) hN)
  rw [Real.dist_eq, abs_lt] at hb1 hb2
  have hsplitL : ∑ i ∈ Finset.range K,
      ((countIn x ((i:ℝ)/K) (((i:ℝ)+1)/K) N : ℝ)/N) * g ((i:ℝ)/K)
      = (∑ i ∈ Finset.range K,
          (countIn x ((i:ℝ)/K) (((i:ℝ)+1)/K) N : ℝ) * g ((i:ℝ)/K)) / N := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hsplitU : ∑ i ∈ Finset.range K,
      ((countIn x ((i:ℝ)/K) (((i:ℝ)+1)/K) N : ℝ)/N) * g (((i:ℝ)+1)/K)
      = (∑ i ∈ Finset.range K,
          (countIn x ((i:ℝ)/K) (((i:ℝ)+1)/K) N : ℝ) * g (((i:ℝ)+1)/K)) / N := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hlow : ∑ i ∈ Finset.range K,
      ((countIn x ((i:ℝ)/K) (((i:ℝ)+1)/K) N : ℝ)/N) * g ((i:ℝ)/K)
      ≤ (∑ n ∈ Finset.range N, g (Int.fract (x n))) / N := by
    rw [hsplitL, div_le_div_iff_of_pos_right hNR]
    exact sum_lower_bound hg x hK N
  have hup : (∑ n ∈ Finset.range N, g (Int.fract (x n))) / N
      ≤ ∑ i ∈ Finset.range K,
        ((countIn x ((i:ℝ)/K) (((i:ℝ)+1)/K) N : ℝ)/N) * g (((i:ℝ)+1)/K) := by
    rw [hsplitU, div_le_div_iff_of_pos_right hNR]
    exact sum_upper_bound hg x hK N
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [hb1.1, hb1.2, hb2.1, hb2.2]

/-- Version of `tendsto_average_of_monotone` for functions monotone only on `[0,1]`. -/
theorem tendsto_average_of_monotoneOn {x : ℕ → ℝ} (hx : UniformlyDistributedMod1 x)
    {g : ℝ → ℝ} (hg : MonotoneOn g (Set.Icc (0:ℝ) 1)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, g (Int.fract (x n))) / N) atTop
      (𝓝 (∫ t in (0:ℝ)..1, g t)) := by
  set G : ℝ → ℝ := fun y => g (min 1 (max 0 y)) with hGdef
  have hmem : ∀ y : ℝ, min 1 (max 0 y) ∈ Set.Icc (0:ℝ) 1 :=
    fun y => ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩
  have hGmono : Monotone G := fun a b hab =>
    hg (hmem a) (hmem b) (min_le_min le_rfl (max_le_max le_rfl hab))
  have hGeq : Set.EqOn g G (Set.Icc (0:ℝ) 1) := by
    intro y hy
    simp [hGdef, max_eq_right hy.1, min_eq_right hy.2]
  have h1 : ∀ n : ℕ, g (Int.fract (x n)) = G (Int.fract (x n)) := fun n =>
    hGeq ⟨Int.fract_nonneg _, le_of_lt (Int.fract_lt_one _)⟩
  have h2 : (∫ t in (0:ℝ)..1, g t) = ∫ t in (0:ℝ)..1, G t :=
    intervalIntegral.integral_congr (by rwa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)])
  simp only [h1, h2]
  exact tendsto_average_of_monotone hx hGmono

/-- **Equidistribution against functions of bounded variation.**
If a sequence `x : ℕ → ℝ` is uniformly distributed mod 1, then for every function `f` of bounded
variation on `[0,1]` the averages `(1/N) ∑_{n < N} f (fract (x n))` converge to `∫₀¹ f`. -/
theorem equidistribution_of_BV_uniform {x : ℕ → ℝ} (hx : UniformlyDistributedMod1 x)
    {f : ℝ → ℝ} (hf : BoundedVariationOn f (Set.Icc (0:ℝ) 1)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (Int.fract (x n))) / N) atTop
      (𝓝 (∫ t in (0:ℝ)..1, f t)) := by
  obtain ⟨p, q, hp, hq, rfl⟩ := hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  have huIcc : Set.uIcc (0:ℝ) 1 = Set.Icc (0:ℝ) 1 := Set.uIcc_of_le (by norm_num)
  have hpi : IntervalIntegrable p volume 0 1 := MonotoneOn.intervalIntegrable (by rw [huIcc]; exact hp)
  have hqi : IntervalIntegrable q volume 0 1 := MonotoneOn.intervalIntegrable (by rw [huIcc]; exact hq)
  have hint : (∫ t in (0:ℝ)..1, (p - q) t)
      = (∫ t in (0:ℝ)..1, p t) - ∫ t in (0:ℝ)..1, q t := by
    simp only [Pi.sub_apply]
    exact intervalIntegral.integral_sub hpi hqi
  have hsum : ∀ N : ℕ, (∑ n ∈ Finset.range N, (p - q) (Int.fract (x n))) / N
      = (∑ n ∈ Finset.range N, p (Int.fract (x n))) / N
        - (∑ n ∈ Finset.range N, q (Int.fract (x n))) / N := by
    intro N
    simp [Pi.sub_apply, Finset.sum_sub_distrib, sub_div]
  simp only [hsum, hint]
  exact (tendsto_average_of_monotoneOn hx hp).sub (tendsto_average_of_monotoneOn hx hq)

end EquidistributionBVReduction
end Brockian

