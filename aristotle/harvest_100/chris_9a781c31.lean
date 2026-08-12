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

open Filter Set MeasureTheory
open scoped Topology BigOperators Classical

namespace Brockian.EquidistributionBVReduction

/-- The Cesàro average of `f` along the fractional parts of the sequence `u`. -/
noncomputable def avg (u : ℕ → ℝ) (f : ℝ → ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.range N, f (Int.fract (u n))) / N

/-- `u` is uniformly distributed mod one: the proportion of the first `N` terms whose fractional
part lies in a subinterval `[a, b) ⊆ [0, 1]` tends to the length `b - a`. -/
def UniformlyDistributedMod1 (u : ℕ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
    Tendsto (fun N : ℕ =>
      (((Finset.range N).filter (fun n => Int.fract (u n) ∈ Set.Ico a b)).card : ℝ) / N)
      atTop (𝓝 (b - a))

/-- A step function subordinate to the uniform partition of `[0,1)` into `m` pieces. -/
noncomputable def stepFn (m : ℕ) (c : ℕ → ℝ) : ℝ → ℝ := fun x =>
  ∑ i ∈ Finset.range m, c i * Set.indicator (Set.Ico ((i : ℝ) / m) (((i : ℝ) + 1) / m))
    (fun _ => (1 : ℝ)) x

section Averages

lemma avg_indicator (u : ℕ → ℝ) (a b : ℝ) (N : ℕ) :
    avg u (Set.indicator (Set.Ico a b) (fun _ => (1 : ℝ))) N =
      (((Finset.range N).filter (fun n => Int.fract (u n) ∈ Set.Ico a b)).card : ℝ) / N := by
  unfold avg
  congr 1
  rw [← Finset.sum_boole]
  exact Finset.sum_congr rfl fun n _ => by simp [Set.indicator_apply]

lemma tendsto_avg_indicator {u : ℕ → ℝ} (hu : UniformlyDistributedMod1 u) (a b : ℝ)
    (h0 : 0 ≤ a) (hab : a ≤ b) (h1 : b ≤ 1) :
    Tendsto (avg u (Set.indicator (Set.Ico a b) (fun _ => (1 : ℝ)))) atTop (𝓝 (b - a)) := by
  have h : avg u (Set.indicator (Set.Ico a b) (fun _ => (1 : ℝ))) =
      fun N : ℕ =>
        (((Finset.range N).filter (fun n => Int.fract (u n) ∈ Set.Ico a b)).card : ℝ) / N :=
    funext (avg_indicator u a b)
  rw [h]
  exact hu a b h0 hab h1

lemma avg_stepFn (u : ℕ → ℝ) (m : ℕ) (c : ℕ → ℝ) (N : ℕ) :
    avg u (stepFn m c) N =
      ∑ i ∈ Finset.range m, c i *
        avg u (Set.indicator (Set.Ico ((i : ℝ) / m) (((i : ℝ) + 1) / m)) (fun _ => (1 : ℝ))) N := by
  simp only [avg, stepFn, Finset.sum_div, mul_div_assoc]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm

lemma tendsto_avg_stepFn {u : ℕ → ℝ} (hu : UniformlyDistributedMod1 u) {m : ℕ} (hm : 0 < m)
    (c : ℕ → ℝ) :
    Tendsto (avg u (stepFn m c)) atTop (𝓝 ((∑ i ∈ Finset.range m, c i) / m)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h : avg u (stepFn m c) = fun N : ℕ =>
      ∑ i ∈ Finset.range m, c i *
        avg u (Set.indicator (Set.Ico ((i : ℝ) / m) (((i : ℝ) + 1) / m)) (fun _ => (1 : ℝ))) N :=
    funext (avg_stepFn u m c)
  rw [h]
  have hlim : Tendsto (fun N : ℕ =>
      ∑ i ∈ Finset.range m, c i *
        avg u (Set.indicator (Set.Ico ((i : ℝ) / m) (((i : ℝ) + 1) / m)) (fun _ => (1 : ℝ))) N)
      atTop (𝓝 (∑ i ∈ Finset.range m, c i * (1 / m))) := by
    apply tendsto_finset_sum
    intro i hi
    have hi' : i < m := Finset.mem_range.mp hi
    have h0 : (0 : ℝ) ≤ (i : ℝ) / m := by positivity
    have hab : (i : ℝ) / m ≤ ((i : ℝ) + 1) / m := by gcongr; linarith
    have h1 : ((i : ℝ) + 1) / m ≤ 1 := by
      rw [div_le_one hm']
      have : (i : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hi'
      linarith
    have hlen : ((i : ℝ) + 1) / m - (i : ℝ) / m = 1 / m := by field_simp; ring
    have := tendsto_avg_indicator hu ((i : ℝ) / m) (((i : ℝ) + 1) / m) h0 hab h1
    rw [hlen] at this
    exact tendsto_const_nhds.mul this
  simpa [Finset.sum_div, mul_one_div] using hlim

lemma avg_mono (u : ℕ → ℝ) {f g : ℝ → ℝ} (h : ∀ x ∈ Set.Ico (0 : ℝ) 1, f x ≤ g x) (N : ℕ) :
    avg u f N ≤ avg u g N := by
  unfold avg
  have hsum : ∑ n ∈ Finset.range N, f (Int.fract (u n))
      ≤ ∑ n ∈ Finset.range N, g (Int.fract (u n)) := by
    refine Finset.sum_le_sum fun n _ => h _ ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  gcongr

end Averages

section StepFunctions

lemma stepFn_apply {m : ℕ} (c : ℕ → ℝ) {x : ℝ} {j : ℕ} (hj : j < m)
    (hx : x ∈ Set.Ico ((j : ℝ) / m) (((j : ℝ) + 1) / m)) : stepFn m c x = c j := by
  have hm : (0 : ℝ) < m := by
    have : 0 < m := lt_of_le_of_lt (Nat.zero_le j) hj
    exact_mod_cast this
  unfold stepFn
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr hj)]
  · rw [Set.indicator_of_mem hx]; ring
  · intro i _ hij
    have hnot : x ∉ Set.Ico ((i : ℝ) / m) (((i : ℝ) + 1) / m) := by
      rcases lt_or_gt_of_ne hij with h | h
      · have hij' : ((i : ℝ) + 1) ≤ (j : ℝ) := by exact_mod_cast h
        have hle : ((i : ℝ) + 1) / m ≤ (j : ℝ) / m := by gcongr
        intro hmem
        exact absurd (lt_of_lt_of_le hmem.2 (hle.trans hx.1)) (lt_irrefl _)
      · have hij' : ((j : ℝ) + 1) ≤ (i : ℝ) := by exact_mod_cast h
        have hle : ((j : ℝ) + 1) / m ≤ (i : ℝ) / m := by gcongr
        intro hmem
        exact absurd (lt_of_lt_of_le hx.2 (hle.trans hmem.1)) (lt_irrefl _)
    rw [Set.indicator_of_notMem hnot]; ring

lemma exists_mem_partition {m : ℕ} (hm : 0 < m) {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    ∃ j < m, x ∈ Set.Ico ((j : ℝ) / m) (((j : ℝ) + 1) / m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hnn : (0 : ℝ) ≤ (m : ℝ) * x := mul_nonneg hm'.le hx.1
  refine ⟨⌊(m : ℝ) * x⌋₊, ?_, ?_, ?_⟩
  · have h1 : (m : ℝ) * x < m := by nlinarith [hx.2]
    exact (Nat.floor_lt hnn).mpr (by exact_mod_cast h1)
  · rw [div_le_iff₀ hm']
    linarith [Nat.floor_le hnn]
  · rw [lt_div_iff₀ hm']
    linarith [Nat.lt_floor_add_one ((m : ℝ) * x)]

lemma stepFn_lower_le {f : ℝ → ℝ} (hf : MonotoneOn f (Set.Icc 0 1)) {m : ℕ} (hm : 0 < m)
    {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    stepFn m (fun i => f ((i : ℝ) / m)) x ≤ f x := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨j, hj, hxj⟩ := exists_mem_partition hm hx
  rw [stepFn_apply _ hj hxj]
  have h0 : (0 : ℝ) ≤ (j : ℝ) / m := by positivity
  have h1 : (j : ℝ) / m ≤ 1 := by
    rw [div_le_one hm']
    exact_mod_cast hj.le
  exact hf ⟨h0, h1⟩ ⟨hx.1, hx.2.le⟩ hxj.1

lemma le_stepFn_upper {f : ℝ → ℝ} (hf : MonotoneOn f (Set.Icc 0 1)) {m : ℕ} (hm : 0 < m)
    {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    f x ≤ stepFn m (fun i => f (((i : ℝ) + 1) / m)) x := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨j, hj, hxj⟩ := exists_mem_partition hm hx
  rw [stepFn_apply _ hj hxj]
  have h0 : (0 : ℝ) ≤ ((j : ℝ) + 1) / m := by positivity
  have h1 : ((j : ℝ) + 1) / m ≤ 1 := by
    rw [div_le_one hm']
    have : (j : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hj
    linarith
  exact hf ⟨hx.1, hx.2.le⟩ ⟨h0, h1⟩ hxj.2.le

end StepFunctions

section RiemannSums

lemma intervalIntegrable_of_monotoneOn {f : ℝ → ℝ} (hf : MonotoneOn f (Set.Icc 0 1))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    IntervalIntegrable f MeasureTheory.volume a b := by
  apply MonotoneOn.intervalIntegrable
  rw [Set.uIcc_of_le hab]
  exact hf.mono (Set.Icc_subset_Icc ha hb)

lemma lower_sum_le_integral {f : ℝ → ℝ} (hf : MonotoneOn f (Set.Icc 0 1)) {m : ℕ} (hm : 0 < m) :
    (∑ i ∈ Finset.range m, f ((i : ℝ) / m)) / m ≤ ∫ x in (0 : ℝ)..1, f x := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set a : ℕ → ℝ := fun i => (i : ℝ) / m with ha
  have hmono : ∀ i : ℕ, a i ≤ a (i + 1) := by
    intro i; simp only [ha]; gcongr; exact Nat.le_succ i
  have h0 : a 0 = 0 := by simp [ha]
  have ham : a m = 1 := by simp only [ha]; field_simp
  have hnn : ∀ i : ℕ, 0 ≤ a i := by intro i; simp only [ha]; positivity
  have hle1 : ∀ i ≤ m, a i ≤ 1 := by
    intro i hi
    simp only [ha]
    rw [div_le_one hm']
    exact_mod_cast hi
  have hsum : ∑ i ∈ Finset.range m, ∫ x in (a i)..(a (i + 1)), f x = ∫ x in (0 : ℝ)..1, f x := by
    rw [intervalIntegral.sum_integral_adjacent_intervals (fun k hk =>
      intervalIntegrable_of_monotoneOn hf (hnn k) (hmono k) (hle1 (k + 1) hk)), h0, ham]
  rw [← hsum, Finset.sum_div]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i < m := Finset.mem_range.mp hi
  have hstep : f (a i) / m = ∫ _x in (a i)..(a (i + 1)), f (a i) := by
    rw [intervalIntegral.integral_const]
    have hd : a (i + 1) - a i = 1 / m := by simp only [ha]; push_cast; field_simp; ring
    rw [hd]
    simp [div_eq_inv_mul]
  rw [hstep]
  apply intervalIntegral.integral_mono_on (hmono i) intervalIntegrable_const
    (intervalIntegrable_of_monotoneOn hf (hnn i) (hmono i) (hle1 (i + 1) hi'))
  intro x hx
  exact hf ⟨hnn i, hle1 i hi'.le⟩ ⟨le_trans (hnn i) hx.1, le_trans hx.2 (hle1 (i + 1) hi')⟩ hx.1

lemma integral_le_upper_sum {f : ℝ → ℝ} (hf : MonotoneOn f (Set.Icc 0 1)) {m : ℕ} (hm : 0 < m) :
    (∫ x in (0 : ℝ)..1, f x) ≤ (∑ i ∈ Finset.range m, f (((i : ℝ) + 1) / m)) / m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set a : ℕ → ℝ := fun i => (i : ℝ) / m with ha
  have hmono : ∀ i : ℕ, a i ≤ a (i + 1) := by
    intro i; simp only [ha]; gcongr; exact Nat.le_succ i
  have h0 : a 0 = 0 := by simp [ha]
  have ham : a m = 1 := by simp only [ha]; field_simp
  have hnn : ∀ i : ℕ, 0 ≤ a i := by intro i; simp only [ha]; positivity
  have hle1 : ∀ i ≤ m, a i ≤ 1 := by
    intro i hi
    simp only [ha]
    rw [div_le_one hm']
    exact_mod_cast hi
  have hsum : ∑ i ∈ Finset.range m, ∫ x in (a i)..(a (i + 1)), f x = ∫ x in (0 : ℝ)..1, f x := by
    rw [intervalIntegral.sum_integral_adjacent_intervals (fun k hk =>
      intervalIntegrable_of_monotoneOn hf (hnn k) (hmono k) (hle1 (k + 1) hk)), h0, ham]
  rw [← hsum, Finset.sum_div]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i < m := Finset.mem_range.mp hi
  have hcast : ((i : ℝ) + 1) / m = a (i + 1) := by simp only [ha]; push_cast; ring
  rw [hcast]
  have hstep : f (a (i + 1)) / m = ∫ _x in (a i)..(a (i + 1)), f (a (i + 1)) := by
    rw [intervalIntegral.integral_const]
    have hd : a (i + 1) - a i = 1 / m := by simp only [ha]; push_cast; field_simp; ring
    rw [hd]
    simp [div_eq_inv_mul]
  rw [hstep]
  apply intervalIntegral.integral_mono_on (hmono i)
    (intervalIntegrable_of_monotoneOn hf (hnn i) (hmono i) (hle1 (i + 1) hi'))
    intervalIntegrable_const
  intro x hx
  exact hf ⟨le_trans (hnn i) hx.1, le_trans hx.2 (hle1 (i + 1) hi')⟩
    ⟨hnn (i + 1), hle1 (i + 1) hi'⟩ hx.2

lemma upper_sub_lower_sum {f : ℝ → ℝ} {m : ℕ} :
    (∑ i ∈ Finset.range m, f (((i : ℝ) + 1) / m)) / m
      - (∑ i ∈ Finset.range m, f ((i : ℝ) / m)) / m = (f (m / m) - f (0 / m)) / m := by
  rw [div_sub_div_same]
  congr 1
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ i ∈ Finset.range m, f (((i : ℝ) + 1) / m) - f ((i : ℝ) / m)
      = (fun j : ℕ => f ((j : ℝ) / m)) (i + 1) - (fun j : ℕ => f ((j : ℝ) / m)) i := by
    intro i _; push_cast; ring_nf
  rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub (fun j : ℕ => f ((j : ℝ) / m))]
  norm_num

end RiemannSums

/-- Uniform distribution mod one implies convergence of the averages for monotone test
functions. -/
theorem tendsto_avg_of_monotoneOn {u : ℕ → ℝ} (hu : UniformlyDistributedMod1 u) {f : ℝ → ℝ}
    (hf : MonotoneOn f (Set.Icc 0 1)) :
    Tendsto (avg u f) atTop (𝓝 (∫ x in (0 : ℝ)..1, f x)) := by
  set I : ℝ := ∫ x in (0 : ℝ)..1, f x with hI
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- choose a fine enough partition
  obtain ⟨m0, hm0⟩ := exists_nat_gt ((f 1 - f 0) * 3 / ε)
  set m : ℕ := m0 + 1 with hmdef
  have hm : 0 < m := Nat.succ_pos _
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmgt : (f 1 - f 0) * 3 / ε < m := by
    refine lt_of_lt_of_le hm0 ?_
    exact_mod_cast Nat.le_succ m0
  have hfine : (f 1 - f 0) / m < ε / 3 := by
    have h1 : (f 1 - f 0) * 3 < m * ε := (div_lt_iff₀ hε).mp hmgt
    rw [div_lt_div_iff₀ hm' (by norm_num : (0 : ℝ) < 3)]
    linarith
  set Sl : ℝ := (∑ i ∈ Finset.range m, f ((i : ℝ) / m)) / m with hSl
  set Su : ℝ := (∑ i ∈ Finset.range m, f (((i : ℝ) + 1) / m)) / m with hSu
  have hlow : Sl ≤ I := lower_sum_le_integral hf hm
  have hupp : I ≤ Su := integral_le_upper_sum hf hm
  have hdiff : Su - Sl = (f 1 - f 0) / m := by
    have h := upper_sub_lower_sum (f := f) (m := m)
    have hmm : ((m : ℝ)) / m = 1 := by field_simp
    have hzz : ((0 : ℝ)) / m = 0 := by simp
    rw [hmm, hzz] at h
    exact h
  -- the two step functions
  have hLtend : Tendsto (avg u (stepFn m (fun i => f ((i : ℝ) / m)))) atTop (𝓝 Sl) :=
    tendsto_avg_stepFn hu hm _
  have hUtend : Tendsto (avg u (stepFn m (fun i => f (((i : ℝ) + 1) / m)))) atTop (𝓝 Su) :=
    tendsto_avg_stepFn hu hm _
  rw [Metric.tendsto_atTop] at hLtend hUtend
  obtain ⟨N1, hN1⟩ := hLtend (ε / 3) (by linarith)
  obtain ⟨N2, hN2⟩ := hUtend (ε / 3) (by linarith)
  refine ⟨max N1 N2, fun N hN => ?_⟩
  have hb1 := hN1 N (le_trans (le_max_left _ _) hN)
  have hb2 := hN2 N (le_trans (le_max_right _ _) hN)
  rw [Real.dist_eq, abs_lt] at hb1 hb2 ⊢
  have hle1 : avg u (stepFn m (fun i => f ((i : ℝ) / m))) N ≤ avg u f N :=
    avg_mono u (fun x hx => stepFn_lower_le hf hm hx) N
  have hle2 : avg u f N ≤ avg u (stepFn m (fun i => f (((i : ℝ) + 1) / m))) N :=
    avg_mono u (fun x hx => le_stepFn_upper hf hm hx) N
  constructor <;> [linarith [hb1.1, hb2.2]; linarith [hb1.1, hb2.2]]

/-- **Equidistribution against functions of bounded variation.**
If `u` is uniformly distributed mod one and `f` has bounded variation on `[0,1]`, then the
Cesàro averages of `f` along the fractional parts of `u` converge to `∫₀¹ f`. -/
theorem equidistribution_of_BV_uniform {u : ℕ → ℝ} (hu : UniformlyDistributedMod1 u) {f : ℝ → ℝ}
    (hf : BoundedVariationOn f (Set.Icc 0 1)) :
    Tendsto (avg u f) atTop (𝓝 (∫ x in (0 : ℝ)..1, f x)) := by
  obtain ⟨p, q, hp, hq, rfl⟩ := hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  have hpi : IntervalIntegrable p MeasureTheory.volume 0 1 :=
    intervalIntegrable_of_monotoneOn hp le_rfl zero_le_one le_rfl
  have hqi : IntervalIntegrable q MeasureTheory.volume 0 1 :=
    intervalIntegrable_of_monotoneOn hq le_rfl zero_le_one le_rfl
  have hint : (∫ x in (0 : ℝ)..1, (p - q) x) =
      (∫ x in (0 : ℝ)..1, p x) - ∫ x in (0 : ℝ)..1, q x := by
    simp [intervalIntegral.integral_sub hpi hqi]
  have havg : avg u (p - q) = fun N => avg u p N - avg u q N := by
    funext N
    simp [avg, Pi.sub_apply, Finset.sum_sub_distrib, sub_div]
  rw [hint, havg]
  exact (tendsto_avg_of_monotoneOn hu hp).sub (tendsto_avg_of_monotoneOn hu hq)

end Brockian.EquidistributionBVReduction

