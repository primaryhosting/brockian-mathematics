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

open Filter Finset MeasureTheory Set
open scoped Topology

namespace Brockian.EquidistributionBVReduction

/-- The frequency with which the fractional parts of the first `N` terms of the sequence `x`
land in the interval `[a, b)`. -/
noncomputable def freq (x : ℕ → ℝ) (a b : ℝ) (N : ℕ) : ℝ :=
  ((((Finset.range N).filter (fun n => Int.fract (x n) ∈ Set.Ico a b)).card : ℝ)) / N

/-- A sequence of reals is *uniformly distributed mod 1* if for every subinterval `[a, b)` of
`[0, 1]` the frequency of the fractional parts of the sequence in `[a, b)` tends to the length
`b - a` of the interval. -/
def UniformlyDistributedMod1 (x : ℕ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → Tendsto (freq x a b) atTop (𝓝 (b - a))

/-- Sanity check: the hypothesis of uniform distribution mod 1 has genuine content; a constant
sequence is not uniformly distributed mod 1. -/
lemma not_uniformlyDistributedMod1_const : ¬ UniformlyDistributedMod1 (fun _ : ℕ => (0:ℝ)) := by
  intro h
  have h2 := h (1/2) 1 (by norm_num) (by norm_num) le_rfl
  have hzero : freq (fun _ : ℕ => (0:ℝ)) (1/2) 1 = fun _ => 0 := by
    funext N
    simp [freq, Int.fract]
  rw [hzero] at h2
  have := tendsto_nhds_unique h2 tendsto_const_nhds
  norm_num at this

section Monotone

variable {x : ℕ → ℝ} {g : ℝ → ℝ}

/-- The fibers of `n ↦ ⌊k * frac (x n)⌋₊` are exactly the sets of indices whose fractional part
lies in the corresponding subinterval of the uniform partition of `[0, 1)` into `k` pieces. -/
lemma fiber_eq_filter_Ico (x : ℕ → ℝ) {k : ℕ} (hk : 0 < k) (N j : ℕ) :
    ((Finset.range N).filter (fun n => ⌊(k : ℝ) * Int.fract (x n)⌋₊ = j)) =
      ((Finset.range N).filter
        (fun n => Int.fract (x n) ∈ Set.Ico ((j : ℝ) / k) (((j : ℝ) + 1) / k))) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  refine Finset.filter_congr (fun n _ => ?_)
  have h0 : (0:ℝ) ≤ (k:ℝ) * Int.fract (x n) := mul_nonneg hk0.le (Int.fract_nonneg _)
  rw [Nat.floor_eq_iff h0, Set.mem_Ico, div_le_iff₀ hk0, lt_div_iff₀ hk0]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith [h1], by linarith [h2]⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

/-- The indices `n < N` are distributed among the `k` subintervals of the uniform partition. -/
lemma index_mem_range (x : ℕ → ℝ) {k : ℕ} (hk : 0 < k) (N : ℕ) :
    ∀ n ∈ Finset.range N, ⌊(k : ℝ) * Int.fract (x n)⌋₊ ∈ Finset.range k := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  intro n _
  have h0 : (0:ℝ) ≤ (k:ℝ) * Int.fract (x n) := mul_nonneg hk0.le (Int.fract_nonneg _)
  rw [Finset.mem_range, Nat.floor_lt h0]
  calc (k:ℝ) * Int.fract (x n) < k * 1 := by
        have := Int.fract_lt_one (x n)
        nlinarith
    _ = k := by ring

/-- Upper sandwich for a Birkhoff-type sum of a monotone function by the counting frequencies of
the uniform partition. -/
lemma sum_le_upper_step (hg : MonotoneOn g (Set.Icc (0 : ℝ) 1)) (x : ℕ → ℝ) {k : ℕ} (hk : 0 < k)
    (N : ℕ) :
    ∑ n ∈ Finset.range N, g (Int.fract (x n)) ≤
      ∑ j ∈ Finset.range k, g (((j : ℝ) + 1) / k) *
        (((Finset.range N).filter
          (fun n => Int.fract (x n) ∈ Set.Ico ((j : ℝ) / k) (((j : ℝ) + 1) / k))).card : ℝ) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  rw [← Finset.sum_fiberwise_of_maps_to (index_mem_range x hk N) (fun n => g (Int.fract (x n)))]
  refine Finset.sum_le_sum (fun j hj => ?_)
  rw [fiber_eq_filter_Ico x hk N j]
  have hjk : ((j:ℝ) + 1) / k ≤ 1 := by
    rw [div_le_one hk0]
    have : j + 1 ≤ k := Finset.mem_range.mp hj
    exact_mod_cast this
  have hjk0 : (0:ℝ) ≤ ((j:ℝ)+1)/k := by positivity
  calc ∑ n ∈ (Finset.range N).filter
          (fun n => Int.fract (x n) ∈ Set.Ico ((j : ℝ) / k) (((j : ℝ) + 1) / k)),
          g (Int.fract (x n))
      ≤ ∑ _n ∈ (Finset.range N).filter
          (fun n => Int.fract (x n) ∈ Set.Ico ((j : ℝ) / k) (((j : ℝ) + 1) / k)),
          g (((j:ℝ)+1)/k) := by
        refine Finset.sum_le_sum (fun n hn => ?_)
        have hmem := (Finset.mem_filter.mp hn).2
        exact hg ⟨Int.fract_nonneg _, le_of_lt (lt_of_lt_of_le hmem.2 hjk)⟩ ⟨hjk0, hjk⟩ hmem.2.le
    _ = g (((j:ℝ)+1)/k) * _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- Lower sandwich for a Birkhoff-type sum of a monotone function by the counting frequencies of
the uniform partition. -/
lemma lower_step_le_sum (hg : MonotoneOn g (Set.Icc (0 : ℝ) 1)) (x : ℕ → ℝ) {k : ℕ} (hk : 0 < k)
    (N : ℕ) :
    ∑ j ∈ Finset.range k, g ((j : ℝ) / k) *
        (((Finset.range N).filter
          (fun n => Int.fract (x n) ∈ Set.Ico ((j : ℝ) / k) (((j : ℝ) + 1) / k))).card : ℝ) ≤
      ∑ n ∈ Finset.range N, g (Int.fract (x n)) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  rw [← Finset.sum_fiberwise_of_maps_to (index_mem_range x hk N) (fun n => g (Int.fract (x n)))]
  refine Finset.sum_le_sum (fun j hj => ?_)
  rw [fiber_eq_filter_Ico x hk N j]
  have hjk : ((j:ℝ) + 1) / k ≤ 1 := by
    rw [div_le_one hk0]
    have : j + 1 ≤ k := Finset.mem_range.mp hj
    exact_mod_cast this
  have hj1 : (j:ℝ)/k ≤ ((j:ℝ)+1)/k := by gcongr; linarith
  have hj0 : (0:ℝ) ≤ (j:ℝ)/k := by positivity
  calc g ((j:ℝ)/k) * _
      = ∑ _n ∈ (Finset.range N).filter
          (fun n => Int.fract (x n) ∈ Set.Ico ((j : ℝ) / k) (((j : ℝ) + 1) / k)),
          g ((j:ℝ)/k) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ n ∈ (Finset.range N).filter
          (fun n => Int.fract (x n) ∈ Set.Ico ((j : ℝ) / k) (((j : ℝ) + 1) / k)),
          g (Int.fract (x n)) := by
        refine Finset.sum_le_sum (fun n hn => ?_)
        have hmem := (Finset.mem_filter.mp hn).2
        exact hg ⟨hj0, hj1.trans hjk⟩
          ⟨Int.fract_nonneg _, le_of_lt (lt_of_lt_of_le hmem.2 hjk)⟩ hmem.1

/-- The lower Riemann sum of a monotone function is at most its integral. -/
lemma lower_sum_le_integral (hg : MonotoneOn g (Set.Icc (0 : ℝ) 1)) {k : ℕ} (hk : 0 < k) :
    ∑ j ∈ Finset.range k, g ((j : ℝ) / k) / k ≤ ∫ t in (0 : ℝ)..1, g t := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  set a : ℕ → ℝ := fun j => (j : ℝ) / k with ha
  have hmem : ∀ j : ℕ, j ≤ k → a j ∈ Set.Icc (0:ℝ) 1 := by
    intro j hj
    refine ⟨by positivity, ?_⟩
    rw [ha]; dsimp only; rw [div_le_one hk0]; exact_mod_cast hj
  have hle : ∀ j : ℕ, a j ≤ a (j+1) := by
    intro j; rw [ha]; dsimp only; gcongr; linarith
  have hsub : ∀ j, j < k → Set.uIcc (a j) (a (j+1)) ⊆ Set.Icc (0:ℝ) 1 := by
    intro j hj
    rw [Set.uIcc_of_le (hle j)]
    exact Set.Icc_subset_Icc (hmem j hj.le).1 (hmem (j+1) hj).2
  have hint : ∀ j < k, IntervalIntegrable g MeasureTheory.volume (a j) (a (j+1)) :=
    fun j hj => (hg.mono (hsub j hj)).intervalIntegrable
  have hsum : ∑ j ∈ Finset.range k, ∫ t in (a j)..(a (j+1)), g t = ∫ t in (0:ℝ)..1, g t := by
    rw [intervalIntegral.sum_integral_adjacent_intervals hint]
    have h0 : a 0 = 0 := by simp [ha]
    have h1 : a k = 1 := by rw [ha]; field_simp
    rw [h0, h1]
  rw [← hsum]
  refine Finset.sum_le_sum (fun j hj => ?_)
  have hjk := Finset.mem_range.mp hj
  have hdiff : a (j+1) - a j = 1/k := by rw [ha]; push_cast; field_simp; ring
  have hconst : ∫ _t in (a j)..(a (j+1)), g (a j) = g (a j) * (1/k) := by
    rw [intervalIntegral.integral_const, hdiff, smul_eq_mul]; ring
  have hmain := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) (hle j)
    (intervalIntegrable_const (c := g (a j))) (hint j hjk)
    (fun t ht => hg (hmem j hjk.le)
      (hsub j hjk (by rw [Set.uIcc_of_le (hle j)]; exact ht)) ht.1)
  rw [hconst] at hmain
  calc g ((j:ℝ)/k) / k = g (a j) * (1/k) := by rw [ha]; ring
    _ ≤ _ := hmain

/-- The integral of a monotone function is at most its upper Riemann sum. -/
lemma integral_le_upper_sum (hg : MonotoneOn g (Set.Icc (0 : ℝ) 1)) {k : ℕ} (hk : 0 < k) :
    (∫ t in (0 : ℝ)..1, g t) ≤ ∑ j ∈ Finset.range k, g (((j : ℝ) + 1) / k) / k := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  set a : ℕ → ℝ := fun j => (j : ℝ) / k with ha
  have hmem : ∀ j : ℕ, j ≤ k → a j ∈ Set.Icc (0:ℝ) 1 := by
    intro j hj
    refine ⟨by positivity, ?_⟩
    rw [ha]; dsimp only; rw [div_le_one hk0]; exact_mod_cast hj
  have hle : ∀ j : ℕ, a j ≤ a (j+1) := by
    intro j; rw [ha]; dsimp only; gcongr; linarith
  have hsub : ∀ j, j < k → Set.uIcc (a j) (a (j+1)) ⊆ Set.Icc (0:ℝ) 1 := by
    intro j hj
    rw [Set.uIcc_of_le (hle j)]
    exact Set.Icc_subset_Icc (hmem j hj.le).1 (hmem (j+1) hj).2
  have hint : ∀ j < k, IntervalIntegrable g MeasureTheory.volume (a j) (a (j+1)) :=
    fun j hj => (hg.mono (hsub j hj)).intervalIntegrable
  have hsum : ∑ j ∈ Finset.range k, ∫ t in (a j)..(a (j+1)), g t = ∫ t in (0:ℝ)..1, g t := by
    rw [intervalIntegral.sum_integral_adjacent_intervals hint]
    have h0 : a 0 = 0 := by simp [ha]
    have h1 : a k = 1 := by rw [ha]; field_simp
    rw [h0, h1]
  rw [← hsum]
  refine Finset.sum_le_sum (fun j hj => ?_)
  have hjk := Finset.mem_range.mp hj
  have hdiff : a (j+1) - a j = 1/k := by rw [ha]; push_cast; field_simp; ring
  have hconst : ∫ _t in (a j)..(a (j+1)), g (a (j+1)) = g (a (j+1)) * (1/k) := by
    rw [intervalIntegral.integral_const, hdiff, smul_eq_mul]; ring
  have hmain := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) (hle j)
    (hint j hjk) (intervalIntegrable_const (c := g (a (j+1))))
    (fun t ht => hg (hsub j hjk (by rw [Set.uIcc_of_le (hle j)]; exact ht))
      (hmem (j+1) hjk) ht.2)
  rw [hconst] at hmain
  calc (∫ t in (a j)..(a (j+1)), g t) ≤ g (a (j+1)) * (1/k) := hmain
    _ = g (((j:ℝ)+1)/k) / k := by rw [ha]; push_cast; ring

/-- Convergence of the weighted counting sums, from uniform distribution. -/
lemma tendsto_step_sum (hx : UniformlyDistributedMod1 x) {k : ℕ} (hk : 0 < k) (c : ℕ → ℝ) :
    Tendsto (fun N : ℕ => ∑ j ∈ Finset.range k, c j *
        ((((Finset.range N).filter
          (fun n => Int.fract (x n) ∈ Set.Ico ((j : ℝ) / k) (((j : ℝ) + 1) / k))).card : ℝ) / N))
      atTop (𝓝 (∑ j ∈ Finset.range k, c j / k)) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  refine tendsto_finset_sum _ (fun j hj => ?_)
  have hjk : j < k := Finset.mem_range.mp hj
  have h1 : (0:ℝ) ≤ (j:ℝ)/k := by positivity
  have h2 : (j:ℝ)/k ≤ ((j:ℝ)+1)/k := by gcongr; linarith
  have h3 : ((j:ℝ)+1)/k ≤ 1 := by
    rw [div_le_one hk0]; have : j + 1 ≤ k := hjk; exact_mod_cast this
  have hlim := (hx ((j:ℝ)/k) (((j:ℝ)+1)/k) h1 h2 h3).const_mul (c j)
  have heq : c j * (((j:ℝ)+1)/k - (j:ℝ)/k) = c j / k := by field_simp; ring
  rw [heq] at hlim
  exact hlim

/-- The Birkhoff averages of a monotone function along a sequence that is uniformly distributed
mod 1 converge to its integral over `[0, 1]`. -/
theorem tendsto_average_of_monotoneOn (hx : UniformlyDistributedMod1 x)
    (hg : MonotoneOn g (Set.Icc (0 : ℝ) 1)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, g (Int.fract (x n))) / N) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, g t)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- choose a fine enough uniform partition
  set M : ℝ := g 1 - g 0 with hM
  have hM0 : 0 ≤ M := by
    have := hg (by norm_num : (0:ℝ) ∈ Set.Icc (0:ℝ) 1) (by norm_num : (1:ℝ) ∈ Set.Icc (0:ℝ) 1)
      (by norm_num)
    simp only [hM]; linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * M / ε)
  set k : ℕ := m + 1 with hkdef
  have hk : 0 < k := Nat.succ_pos m
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hkm : 2 * M / ε < k := by
    refine hm.trans ?_
    rw [hkdef]; push_cast; linarith
  have hMk : M / k < ε / 2 := by
    rw [div_lt_iff₀ hk0]
    rw [div_lt_iff₀ hε] at hkm
    linarith
  -- lower and upper Riemann sums
  set U : ℝ := ∑ j ∈ Finset.range k, g ((j : ℝ) / k) / k with hU
  set V : ℝ := ∑ j ∈ Finset.range k, g (((j : ℝ) + 1) / k) / k with hV
  have hVU : V - U = M / k := by
    rw [hU, hV, ← Finset.sum_sub_distrib]
    have : ∀ j ∈ Finset.range k,
        g (((j : ℝ) + 1) / k) / k - g ((j : ℝ) / k) / k
          = ((fun i : ℕ => g ((i : ℝ) / k) / k) (j + 1))
            - ((fun i : ℕ => g ((i : ℝ) / k) / k) j) := by
      intro j _; dsimp only; push_cast; ring
    rw [Finset.sum_congr rfl this, Finset.sum_range_sub (fun i : ℕ => g ((i : ℝ) / k) / k) k]
    rw [Nat.cast_zero, zero_div]
    have h1 : (k : ℝ) / k = 1 := by field_simp
    rw [h1, hM]
    ring
  have hUI : U ≤ ∫ t in (0:ℝ)..1, g t := lower_sum_le_integral hg hk
  have hIV : (∫ t in (0:ℝ)..1, g t) ≤ V := integral_le_upper_sum hg hk
  -- the counting sums converge
  have hlow := tendsto_step_sum hx hk (fun j => g ((j : ℝ) / k))
  have hupp := tendsto_step_sum hx hk (fun j => g (((j : ℝ) + 1) / k))
  rw [Metric.tendsto_atTop] at hlow hupp
  obtain ⟨N₁, hN₁⟩ := hlow (ε / 4) (by linarith)
  obtain ⟨N₂, hN₂⟩ := hupp (ε / 4) (by linarith)
  refine ⟨max (max N₁ N₂) 1, fun N hN => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ _) hN)
  have hNR : (0:ℝ) < N := by exact_mod_cast hNpos
  have hlowN := hN₁ N hN1
  have huppN := hN₂ N hN2
  rw [Real.dist_eq, abs_lt] at hlowN huppN
  -- the sandwich
  have hcast : ∀ c : ℕ → ℝ,
      ∑ j ∈ Finset.range k, c j *
        ((((Finset.range N).filter
          (fun n => Int.fract (x n) ∈ Set.Ico ((j : ℝ) / k) (((j : ℝ) + 1) / k))).card : ℝ) / N)
        = (∑ j ∈ Finset.range k, c j *
        (((Finset.range N).filter
          (fun n => Int.fract (x n) ∈ Set.Ico ((j : ℝ) / k) (((j : ℝ) + 1) / k))).card : ℝ)) / N
      := by
    intro c
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hlowSand : ∑ j ∈ Finset.range k, g ((j : ℝ) / k) *
        ((((Finset.range N).filter
          (fun n => Int.fract (x n) ∈ Set.Ico ((j : ℝ) / k) (((j : ℝ) + 1) / k))).card : ℝ) / N)
      ≤ (∑ n ∈ Finset.range N, g (Int.fract (x n))) / N := by
    rw [hcast (fun j => g ((j : ℝ) / k))]
    gcongr
    exact lower_step_le_sum hg x hk N
  have huppSand : (∑ n ∈ Finset.range N, g (Int.fract (x n))) / N
      ≤ ∑ j ∈ Finset.range k, g (((j : ℝ) + 1) / k) *
        ((((Finset.range N).filter
          (fun n => Int.fract (x n) ∈ Set.Ico ((j : ℝ) / k) (((j : ℝ) + 1) / k))).card : ℝ) / N)
      := by
    rw [hcast (fun j => g (((j : ℝ) + 1) / k))]
    gcongr
    exact sum_le_upper_step hg x hk N
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> linarith

end Monotone

/-- **Equidistribution theorem for functions of bounded variation.**

If `x : ℕ → ℝ` is uniformly distributed mod 1 and `f` has bounded variation on `[0, 1]`, then the
averages `(1/N) ∑_{n < N} f (frac (x n))` converge to `∫₀¹ f`.  -/
theorem equidistribution_of_BV_uniform {x : ℕ → ℝ} {f : ℝ → ℝ}
    (hx : UniformlyDistributedMod1 x) (hf : BoundedVariationOn f (Set.Icc (0 : ℝ) 1)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (Int.fract (x n))) / N) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, f t)) := by
  obtain ⟨p, q, hp, hq, rfl⟩ := hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  have huIcc : Set.uIcc (0:ℝ) 1 = Set.Icc (0:ℝ) 1 := Set.uIcc_of_le (by norm_num)
  have hpint : IntervalIntegrable p MeasureTheory.volume 0 1 := by
    apply MonotoneOn.intervalIntegrable; rw [huIcc]; exact hp
  have hqint : IntervalIntegrable q MeasureTheory.volume 0 1 := by
    apply MonotoneOn.intervalIntegrable; rw [huIcc]; exact hq
  have hInt : (∫ t in (0:ℝ)..1, (p - q) t)
      = (∫ t in (0:ℝ)..1, p t) - ∫ t in (0:ℝ)..1, q t := by
    simp only [Pi.sub_apply]
    exact intervalIntegral.integral_sub hpint hqint
  have hsplit : ∀ N : ℕ, (∑ n ∈ Finset.range N, (p - q) (Int.fract (x n))) / N
      = (∑ n ∈ Finset.range N, p (Int.fract (x n))) / N
        - (∑ n ∈ Finset.range N, q (Int.fract (x n))) / N := by
    intro N
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, sub_div]
  rw [hInt]
  simp only [hsplit]
  exact (tendsto_average_of_monotoneOn hx hp).sub (tendsto_average_of_monotoneOn hx hq)

end Brockian.EquidistributionBVReduction

