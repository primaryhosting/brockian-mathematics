import Brockian.EquidistributionBVReduction

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

open Filter Set MeasureTheory
open scoped BigOperators Topology

namespace Brockian
namespace EquidistributionBVReduction

/-- The empirical frequency with which the first `N` terms of the sequence `x`
land in the interval `[a, b)`. -/
noncomputable def freq (x : ℕ → ℝ) (a b : ℝ) (N : ℕ) : ℝ :=
  (((Finset.range N).filter (fun n => x n ∈ Set.Ico a b)).card : ℝ) / N

/-- A sequence `x : ℕ → ℝ` taking values in `[0, 1)` is *uniformly distributed* if for every
subinterval `[a, b) ⊆ [0, 1]` the empirical frequency of visits to `[a, b)` tends to its
length `b - a`. -/
def UniformlyDistributed (x : ℕ → ℝ) : Prop :=
  (∀ n, x n ∈ Set.Ico (0 : ℝ) 1) ∧
    ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → Tendsto (freq x a b) atTop (𝓝 (b - a))

/-- The step function on `[0,1)` which takes the value `c i` on the `i`-th interval
`[i / k, (i+1) / k)` of the uniform partition of `[0, 1)` into `k` pieces. -/
noncomputable def stepFun (k : ℕ) (c : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range k, (Set.Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)).indicator (fun _ => c i) t

section Aux

variable {k : ℕ} {c : ℕ → ℝ}

lemma mem_Ico_div_iff (hk : 0 < k) {t : ℝ} (ht : 0 ≤ t) (j : ℕ) :
    t ∈ Set.Ico ((j : ℝ) / k) (((j : ℝ) + 1) / k) ↔ ⌊(k : ℝ) * t⌋₊ = j := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [Set.mem_Ico, div_le_iff₀ hk', lt_div_iff₀ hk', Nat.floor_eq_iff (by positivity)]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

lemma floor_lt_of_mem (hk : 0 < k) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    ⌊(k : ℝ) * t⌋₊ < k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h : (k : ℝ) * t < k := by nlinarith [ht.2, ht.1]
  exact (Nat.floor_lt (by nlinarith [ht.1])).2 (by simpa using h)

lemma stepFun_apply (hk : 0 < k) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    stepFun k c t = c ⌊(k : ℝ) * t⌋₊ := by
  classical
  set i0 := ⌊(k : ℝ) * t⌋₊ with hi0
  have hmem : i0 ∈ Finset.range k := Finset.mem_range.2 (floor_lt_of_mem hk ht)
  rw [stepFun, Finset.sum_eq_single_of_mem i0 hmem]
  · rw [Set.indicator_of_mem]
    exact (mem_Ico_div_iff hk ht.1 i0).2 rfl
  · intro j _ hj
    rw [Set.indicator_of_notMem]
    intro hcon
    exact hj ((mem_Ico_div_iff hk ht.1 j).1 hcon).symm

lemma sum_stepFun (x : ℕ → ℝ) (k : ℕ) (c : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, stepFun k c (x n)
      = ∑ i ∈ Finset.range k,
          c i * (((Finset.range N).filter
            (fun n => x n ∈ Set.Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k))).card : ℝ) := by
  classical
  simp only [stepFun]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.card_filter]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h : x n ∈ Set.Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)
  · simp [h]
  · simp [h]

lemma tendsto_avg_stepFun {x : ℕ → ℝ} (hx : UniformlyDistributed x) (hk : 0 < k) (c : ℕ → ℝ) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, stepFun k c (x n)) / N) atTop
      (𝓝 (∑ i ∈ Finset.range k, c i / k)) := by
  classical
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have key : ∀ N : ℕ, (∑ n ∈ Finset.range N, stepFun k c (x n)) / N
      = ∑ i ∈ Finset.range k, c i * freq x ((i : ℝ) / k) (((i : ℝ) + 1) / k) N := by
    intro N
    rw [sum_stepFun, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [freq, mul_div_assoc]
  simp only [key]
  refine tendsto_finset_sum _ fun i hi => ?_
  have hi' : i < k := Finset.mem_range.1 hi
  have h1 : (0 : ℝ) ≤ (i : ℝ) / k := by positivity
  have h2 : (i : ℝ) / k ≤ ((i : ℝ) + 1) / k := by
    gcongr
    linarith
  have h3 : ((i : ℝ) + 1) / k ≤ 1 := by
    rw [div_le_one hk']
    have : (i : ℝ) + 1 ≤ k := by exact_mod_cast hi'
    linarith
  have h := (hx.2 ((i : ℝ) / k) (((i : ℝ) + 1) / k) h1 h2 h3).const_mul (c i)
  have heq : ((i : ℝ) + 1) / k - (i : ℝ) / k = 1 / k := by
    rw [div_sub_div_same]; norm_num
  rw [heq] at h
  simpa [mul_one_div] using h

end Aux

/-- Lower and upper Riemann sums for a monotone function bracket its integral. -/
lemma riemann_sum_bounds (f : ℝ → ℝ) (hf : MonotoneOn f (Set.Icc (0 : ℝ) 1)) {k : ℕ}
    (hk : 0 < k) :
    (∑ i ∈ Finset.range k, f ((i : ℝ) / k) / k) ≤ (∫ t in (0 : ℝ)..1, f t) ∧
      (∫ t in (0 : ℝ)..1, f t) ≤ ∑ i ∈ Finset.range k, f (((i : ℝ) + 1) / k) / k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  set a : ℕ → ℝ := fun i => (i : ℝ) / k with ha
  have hstep : ∀ i : ℕ, a (i + 1) - a i = 1 / k := by
    intro i
    simp only [ha]
    push_cast
    field_simp
    ring
  have hle : ∀ i : ℕ, a i ≤ a (i + 1) := by
    intro i
    have := hstep i
    have : (0 : ℝ) < 1 / k := by positivity
    linarith [hstep i]
  have hsubset : ∀ i, i < k → Set.Icc (a i) (a (i + 1)) ⊆ Set.Icc (0 : ℝ) 1 := by
    intro i hi
    apply Set.Icc_subset_Icc
    · simp only [ha]; positivity
    · simp only [ha]
      rw [div_le_one hk']
      have : (i : ℝ) + 1 ≤ k := by exact_mod_cast hi
      push_cast
      linarith
  have hmono' : ∀ i, i < k → MonotoneOn f (Set.uIcc (a i) (a (i + 1))) := by
    intro i hi
    rw [Set.uIcc_of_le (hle i)]
    exact hf.mono (hsubset i hi)
  have hint : ∀ i < k, IntervalIntegrable f volume (a i) (a (i + 1)) := fun i hi =>
    (hmono' i hi).intervalIntegrable
  have hsplit : ∑ i ∈ Finset.range k, ∫ t in (a i)..(a (i + 1)), f t
      = ∫ t in (a 0)..(a k), f t := intervalIntegral.sum_integral_adjacent_intervals hint
  have ha0 : a 0 = 0 := by simp [ha]
  have hak : a k = 1 := by
    simp only [ha]
    field_simp
  rw [ha0, hak] at hsplit
  constructor
  · rw [← hsplit]
    refine Finset.sum_le_sum fun i hi => ?_
    have hik : i < k := Finset.mem_range.1 hi
    have hlow : ∀ t ∈ Set.Icc (a i) (a (i + 1)), f (a i) ≤ f t := by
      intro t ht
      exact hf (hsubset i hik (Set.mem_Icc.2 ⟨le_rfl, hle i⟩)) (hsubset i hik ht) ht.1
    have := intervalIntegral.integral_mono_on (μ := volume) (hle i)
      (intervalIntegrable_const (c := f (a i))) (hint i hik) hlow
    rw [intervalIntegral.integral_const, hstep i] at this
    simpa [ha, smul_eq_mul, div_eq_inv_mul] using this
  · rw [← hsplit]
    refine Finset.sum_le_sum fun i hi => ?_
    have hik : i < k := Finset.mem_range.1 hi
    have hhigh : ∀ t ∈ Set.Icc (a i) (a (i + 1)), f t ≤ f (a (i + 1)) := by
      intro t ht
      exact hf (hsubset i hik ht) (hsubset i hik (Set.mem_Icc.2 ⟨hle i, le_rfl⟩)) ht.2
    have := intervalIntegral.integral_mono_on (μ := volume) (hle i) (hint i hik)
      (intervalIntegrable_const (c := f (a (i + 1)))) hhigh
    rw [intervalIntegral.integral_const, hstep i] at this
    have hcast : a (i + 1) = ((i : ℝ) + 1) / k := by simp only [ha]; push_cast; ring
    rw [hcast] at this ⊢
    simpa [smul_eq_mul, div_eq_inv_mul] using this

lemma riemann_sum_gap (f : ℝ → ℝ) {k : ℕ} (hk : 0 < k) :
    (∑ i ∈ Finset.range k, f (((i : ℝ) + 1) / k) / k)
      - (∑ i ∈ Finset.range k, f ((i : ℝ) / k) / k) = (f 1 - f 0) / k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  set g : ℕ → ℝ := fun j => f ((j : ℝ) / k) / k with hg
  have hcongr : ∀ i ∈ Finset.range k,
      f (((i : ℝ) + 1) / k) / k - f ((i : ℝ) / k) / k = g (i + 1) - g i := by
    intro i _
    simp only [hg]
    push_cast
    ring_nf
  rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl hcongr, Finset.sum_range_sub g]
  simp only [hg]
  rw [div_self (ne_of_gt hk')]
  simp [sub_div]

/-- Equidistribution test for monotone functions. -/
theorem tendsto_average_of_monotoneOn {x : ℕ → ℝ} (hx : UniformlyDistributed x) (f : ℝ → ℝ)
    (hf : MonotoneOn f (Set.Icc (0 : ℝ) 1)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (x n)) / N) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, f t)) := by
  classical
  have hD : 0 ≤ f 1 - f 0 := by
    have := hf (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
      (by norm_num : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1) (by norm_num)
    linarith
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hkgt⟩ := exists_nat_gt (2 * (f 1 - f 0) / ε + 1)
  have hpos : 0 ≤ 2 * (f 1 - f 0) / ε := div_nonneg (by linarith) hε.le
  have hk1 : (1 : ℝ) < (k : ℝ) := by linarith
  have hk0 : 0 < k := by
    have : (1 : ℕ) < k := by exact_mod_cast hk1
    omega
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk0
  have hgap : (f 1 - f 0) / k < ε / 2 := by
    rw [div_lt_iff₀ hk']
    have h2 : 2 * (f 1 - f 0) / ε < k := by linarith
    rw [div_lt_iff₀ hε] at h2
    linarith
  obtain ⟨hLI, hIU⟩ := riemann_sum_bounds f hf hk0
  have hUL := riemann_sum_gap f hk0
  have hlow : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, stepFun k (fun i => f ((i : ℝ) / k)) (x n)) / N) atTop
      (𝓝 (∑ i ∈ Finset.range k, f ((i : ℝ) / k) / k)) := tendsto_avg_stepFun hx hk0 _
  have hhigh : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, stepFun k (fun i => f (((i : ℝ) + 1) / k)) (x n)) / N) atTop
      (𝓝 (∑ i ∈ Finset.range k, f (((i : ℝ) + 1) / k) / k)) := tendsto_avg_stepFun hx hk0 _
  rw [Metric.tendsto_atTop] at hlow hhigh
  obtain ⟨N1, hN1⟩ := hlow (ε / 4) (by linarith)
  obtain ⟨N2, hN2⟩ := hhigh (ε / 4) (by linarith)
  refine ⟨max 1 (max N1 N2), fun N hN => ?_⟩
  have hNone : 1 ≤ N := le_trans (le_max_left _ _) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hNone
  have hN1' := hN1 N (le_trans (le_trans (le_max_left _ _) (le_max_right 1 _)) hN)
  have hN2' := hN2 N (le_trans (le_trans (le_max_right _ _) (le_max_right 1 _)) hN)
  have hptw : ∀ n, stepFun k (fun i => f ((i : ℝ) / k)) (x n) ≤ f (x n) ∧
      f (x n) ≤ stepFun k (fun i => f (((i : ℝ) + 1) / k)) (x n) := by
    intro n
    have ht := hx.1 n
    have hi0 : ⌊(k : ℝ) * x n⌋₊ < k := floor_lt_of_mem hk0 ht
    have hmem : x n ∈ Set.Ico ((⌊(k : ℝ) * x n⌋₊ : ℝ) / k) (((⌊(k : ℝ) * x n⌋₊ : ℝ) + 1) / k) :=
      (mem_Ico_div_iff hk0 ht.1 _).2 rfl
    have hile : ((⌊(k : ℝ) * x n⌋₊ : ℝ) + 1) / k ≤ 1 := by
      rw [div_le_one hk']
      have : ((⌊(k : ℝ) * x n⌋₊ : ℝ)) + 1 ≤ k := by exact_mod_cast hi0
      linarith
    have hmono2 : ((⌊(k : ℝ) * x n⌋₊ : ℝ)) / k ≤ ((⌊(k : ℝ) * x n⌋₊ : ℝ) + 1) / k := by
      gcongr
      linarith
    have h1 : ((⌊(k : ℝ) * x n⌋₊ : ℝ)) / k ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by positivity, le_trans hmono2 hile⟩
    have h2 : ((⌊(k : ℝ) * x n⌋₊ : ℝ) + 1) / k ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨le_trans (by positivity) hmono2, hile⟩
    have hxmem : x n ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
    refine ⟨?_, ?_⟩
    · rw [stepFun_apply hk0 ht]
      exact hf h1 hxmem hmem.1
    · rw [stepFun_apply hk0 ht]
      exact hf hxmem h2 hmem.2.le
  have hd1 : (∑ n ∈ Finset.range N, stepFun k (fun i => f ((i : ℝ) / k)) (x n)) / N
      ≤ (∑ n ∈ Finset.range N, f (x n)) / N := by
    gcongr with n hn
    exact (hptw n).1
  have hd2 : (∑ n ∈ Finset.range N, f (x n)) / N
      ≤ (∑ n ∈ Finset.range N, stepFun k (fun i => f (((i : ℝ) + 1) / k)) (x n)) / N := by
    gcongr with n hn
    exact (hptw n).2
  rw [Real.dist_eq, abs_lt] at hN1' hN2' ⊢
  constructor <;> linarith [hN1'.1, hN1'.2, hN2'.1, hN2'.2]

/-- **Equidistribution test for functions of bounded variation.**
If `x` is a uniformly distributed sequence in `[0,1)` and `f` has bounded variation on `[0,1]`,
then the averages of `f` along the sequence converge to the integral of `f` over `[0,1]`. -/
theorem equidistribution_of_BV_uniform {x : ℕ → ℝ} (hx : UniformlyDistributed x) (f : ℝ → ℝ)
    (hf : BoundedVariationOn f (Set.Icc (0 : ℝ) 1)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (x n)) / N) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, f t)) := by
  obtain ⟨p, q, hp, hq, hpq⟩ :=
    hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  have huIcc : Set.uIcc (0 : ℝ) 1 = Set.Icc (0 : ℝ) 1 := Set.uIcc_of_le (by norm_num)
  have hpi : IntervalIntegrable p volume 0 1 :=
    MonotoneOn.intervalIntegrable (by rw [huIcc]; exact hp)
  have hqi : IntervalIntegrable q volume 0 1 :=
    MonotoneOn.intervalIntegrable (by rw [huIcc]; exact hq)
  have hIsub : (∫ t in (0 : ℝ)..1, f t)
      = (∫ t in (0 : ℝ)..1, p t) - ∫ t in (0 : ℝ)..1, q t := by
    rw [hpq]
    simpa only [Pi.sub_apply] using intervalIntegral.integral_sub hpi hqi
  have hsum : ∀ N : ℕ, (∑ n ∈ Finset.range N, f (x n)) / N
      = (∑ n ∈ Finset.range N, p (x n)) / N - (∑ n ∈ Finset.range N, q (x n)) / N := by
    intro N
    rw [hpq]
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, sub_div]
  simp only [hsum, hIsub]
  exact (tendsto_average_of_monotoneOn hx p hp).sub (tendsto_average_of_monotoneOn hx q hq)

end EquidistributionBVReduction
end Brockian

