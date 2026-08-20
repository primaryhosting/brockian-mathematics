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

/-!
# Equidistribution Of BV Uniform
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Brockian.EquidistributionBVReduction

open Filter Finset

/-- `countBelow x N a` is the number of indices `n < N` whose fractional part is `< a`. -/
noncomputable def countBelow (x : ℕ → ℝ) (N : ℕ) (a : ℝ) : ℕ :=
  ((Finset.range N).filter (fun n => Int.fract (x n) < a)).card

/-- The empirical distribution function of the first `N` fractional parts. -/
noncomputable def edf (x : ℕ → ℝ) (N : ℕ) (a : ℝ) : ℝ := (countBelow x N a : ℝ) / N

/-- A sequence `x : ℕ → ℝ` is uniformly distributed mod one when, for every `a ∈ [0,1]`,
the proportion of the first `N` fractional parts lying below `a` tends to `a`. -/
def UniformlyDistributedMod1 (x : ℕ → ℝ) : Prop :=
  ∀ a ∈ Set.Icc (0:ℝ) 1, Tendsto (fun N => edf x N a) atTop (nhds a)

/-- The set of indices `n < N` whose fractional part lies in `[j/k, (j+1)/k)`. -/
noncomputable def bin (x : ℕ → ℝ) (N k j : ℕ) : Finset ℕ :=
  (Finset.range N).filter
    (fun n => (j:ℝ)/k ≤ Int.fract (x n) ∧ Int.fract (x n) < ((j:ℝ)+1)/k)

/-- The bins partition `range N`, so summing over the bins recovers the full sum. -/
lemma sum_bin (x : ℕ → ℝ) (g : ℝ → ℝ) (N k : ℕ) (hk : 0 < k) :
    ∑ j ∈ Finset.range k, ∑ n ∈ bin x N k j, g (Int.fract (x n))
      = ∑ n ∈ Finset.range N, g (Int.fract (x n)) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hmaps : ∀ n ∈ Finset.range N, ⌊(k:ℝ) * Int.fract (x n)⌋₊ ∈ Finset.range k := by
    intro n _
    have h0 : (0:ℝ) ≤ (k:ℝ) * Int.fract (x n) :=
      mul_nonneg (le_of_lt hk0) (Int.fract_nonneg _)
    have h1 : (k:ℝ) * Int.fract (x n) < k := by
      have := Int.fract_lt_one (x n)
      nlinarith
    simpa [Finset.mem_range] using (Nat.floor_lt h0).2 (by exact_mod_cast h1)
  have hfiber : ∀ j : ℕ,
      ((Finset.range N).filter (fun n => ⌊(k:ℝ) * Int.fract (x n)⌋₊ = j)) = bin x N k j := by
    intro j
    ext n
    simp only [bin, Finset.mem_filter, Finset.mem_range, and_congr_right_iff]
    intro _
    have h0 : (0:ℝ) ≤ (k:ℝ) * Int.fract (x n) :=
      mul_nonneg (le_of_lt hk0) (Int.fract_nonneg _)
    rw [Nat.floor_eq_iff h0]
    constructor
    · rintro ⟨hl, hr⟩
      constructor
      · rw [div_le_iff₀ hk0]; linarith [hl]
      · rw [lt_div_iff₀ hk0]; linarith [hr]
    · rintro ⟨hl, hr⟩
      rw [div_le_iff₀ hk0] at hl
      rw [lt_div_iff₀ hk0] at hr
      constructor <;> linarith
  calc ∑ j ∈ Finset.range k, ∑ n ∈ bin x N k j, g (Int.fract (x n))
      = ∑ j ∈ Finset.range k,
          ∑ n ∈ (Finset.range N).filter (fun n => ⌊(k:ℝ) * Int.fract (x n)⌋₊ = j),
            g (Int.fract (x n)) := by
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [hfiber j]
    _ = ∑ n ∈ Finset.range N, g (Int.fract (x n)) :=
        Finset.sum_fiberwise_of_maps_to hmaps _

/-- The cardinality of a bin is the increment of the empirical counting function. -/
lemma card_bin (x : ℕ → ℝ) (N k j : ℕ) (hk : 0 < k) :
    ((bin x N k j).card : ℝ)
      = (countBelow x N (((j:ℝ)+1)/k) : ℝ) - (countBelow x N ((j:ℝ)/k) : ℝ) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hle : (j:ℝ)/k ≤ ((j:ℝ)+1)/k := by
    rw [div_le_div_iff_of_pos_right hk0]
    linarith
  have hsub : (Finset.range N).filter (fun n => Int.fract (x n) < (j:ℝ)/k) ⊆
      (Finset.range N).filter (fun n => Int.fract (x n) < ((j:ℝ)+1)/k) := by
    intro n hn
    simp only [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, lt_of_lt_of_le hn.2 hle⟩
  have hbin : bin x N k j =
      ((Finset.range N).filter (fun n => Int.fract (x n) < ((j:ℝ)+1)/k)) \
      ((Finset.range N).filter (fun n => Int.fract (x n) < (j:ℝ)/k)) := by
    ext n
    simp only [bin, Finset.mem_filter, Finset.mem_sdiff, not_and, not_lt]
    constructor
    · rintro ⟨hn, hl, hr⟩
      exact ⟨⟨hn, hr⟩, fun _ => hl⟩
    · rintro ⟨⟨hn, hr⟩, h2⟩
      exact ⟨hn, h2 hn, hr⟩
  have hcard : (bin x N k j).card = countBelow x N (((j:ℝ)+1)/k) - countBelow x N ((j:ℝ)/k) := by
    rw [hbin, Finset.card_sdiff, Finset.inter_eq_left.2 hsub]
    rfl
  have hcle : countBelow x N ((j:ℝ)/k) ≤ countBelow x N (((j:ℝ)+1)/k) :=
    Finset.card_le_card hsub
  rw [hcard, Nat.cast_sub hcle]

/-- The subdivision points `j/k` lie in `[0,1]`. -/
lemma pt_mem (k j : ℕ) (hk : 0 < k) (hj : j ≤ k) : ((j:ℝ)/k) ∈ Set.Icc (0:ℝ) 1 := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  refine ⟨by positivity, ?_⟩
  rw [div_le_one hk0]
  exact_mod_cast hj

/-- Each subinterval of the uniform subdivision is contained in `[0,1]`. -/
lemma subinterval_subset (k j : ℕ) (hk : 0 < k) (hj : j + 1 ≤ k) :
    Set.uIcc ((j:ℝ)/k) (((j:ℝ)+1)/k) ⊆ Set.Icc (0:ℝ) 1 := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have h1 : (j:ℝ)/k ≤ ((j:ℝ)+1)/k := by
    rw [div_le_div_iff_of_pos_right hk0]; linarith
  rw [Set.uIcc_of_le h1]
  refine Set.Icc_subset_Icc (pt_mem k j hk (by omega)).1 ?_
  have hcast : ((j:ℝ)+1)/k = ((j+1 : ℕ):ℝ)/k := by push_cast; ring
  rw [hcast]
  exact (pt_mem k (j+1) hk hj).2

/-- A monotone function is interval integrable on each subinterval. -/
lemma integrable_sub (g : ℝ → ℝ) (hg : MonotoneOn g (Set.Icc (0:ℝ) 1)) (k j : ℕ) (hk : 0 < k)
    (hj : j + 1 ≤ k) :
    IntervalIntegrable g MeasureTheory.volume ((j:ℝ)/k) (((j:ℝ)+1)/k) :=
  MonotoneOn.intervalIntegrable (hg.mono (subinterval_subset k j hk hj))

/-- Upper Riemann sums of a monotone function dominate its integral. -/
lemma integral_le_upper_sum (g : ℝ → ℝ) (hg : MonotoneOn g (Set.Icc (0:ℝ) 1)) (k : ℕ)
    (hk : 0 < k) :
    (∫ t in (0:ℝ)..1, g t) ≤ ∑ j ∈ Finset.range k, g (((j:ℝ)+1)/k) / k := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hcast : ∀ j : ℕ, ((j+1 : ℕ):ℝ)/k = ((j:ℝ)+1)/k := by intro j; push_cast; ring
  have hint : ∀ j < k, IntervalIntegrable g MeasureTheory.volume (((j:ℕ):ℝ)/k)
      (((j+1:ℕ):ℝ)/k) := by
    intro j hj
    rw [hcast j]
    exact integrable_sub g hg k j hk hj
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  have ha0 : ((0:ℕ):ℝ)/k = 0 := by simp
  have hak : ((k:ℕ):ℝ)/k = 1 := by field_simp
  rw [ha0, hak] at hsum
  rw [← hsum]
  refine Finset.sum_le_sum ?_
  intro j hj
  simp only [Finset.mem_range] at hj
  have hle : ((j:ℕ):ℝ)/k ≤ ((j+1:ℕ):ℝ)/k := by
    rw [div_le_div_iff_of_pos_right hk0]
    exact_mod_cast Nat.le_succ j
  have hmono : ∀ y ∈ Set.Icc (((j:ℕ):ℝ)/k) (((j+1:ℕ):ℝ)/k), g y ≤ g (((j+1:ℕ):ℝ)/k) := by
    intro y hy
    have hsub := subinterval_subset k j hk hj
    rw [Set.uIcc_of_le (by rw [hcast j] at hle; exact hle)] at hsub
    refine hg (hsub ?_) (pt_mem k (j+1) hk hj) hy.2
    exact ⟨hy.1, by rw [← hcast j]; exact hy.2⟩
  calc (∫ t in (((j:ℕ):ℝ)/k)..(((j+1:ℕ):ℝ)/k), g t)
      ≤ ∫ _t in (((j:ℕ):ℝ)/k)..(((j+1:ℕ):ℝ)/k), g (((j+1:ℕ):ℝ)/k) :=
        intervalIntegral.integral_mono_on hle (hint j hj) intervalIntegrable_const hmono
    _ = g (((j:ℝ)+1)/k) / k := by
        rw [intervalIntegral.integral_const, hcast j]
        simp only [smul_eq_mul]
        field_simp
        ring

/-- Lower Riemann sums of a monotone function are dominated by its integral. -/
lemma lower_sum_le_integral (g : ℝ → ℝ) (hg : MonotoneOn g (Set.Icc (0:ℝ) 1)) (k : ℕ)
    (hk : 0 < k) :
    ∑ j ∈ Finset.range k, g ((j:ℝ)/k) / k ≤ (∫ t in (0:ℝ)..1, g t) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hcast : ∀ j : ℕ, ((j+1 : ℕ):ℝ)/k = ((j:ℝ)+1)/k := by intro j; push_cast; ring
  have hint : ∀ j < k, IntervalIntegrable g MeasureTheory.volume (((j:ℕ):ℝ)/k)
      (((j+1:ℕ):ℝ)/k) := by
    intro j hj
    rw [hcast j]
    exact integrable_sub g hg k j hk hj
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  have ha0 : ((0:ℕ):ℝ)/k = 0 := by simp
  have hak : ((k:ℕ):ℝ)/k = 1 := by field_simp
  rw [ha0, hak] at hsum
  rw [← hsum]
  refine Finset.sum_le_sum ?_
  intro j hj
  simp only [Finset.mem_range] at hj
  have hle : ((j:ℕ):ℝ)/k ≤ ((j+1:ℕ):ℝ)/k := by
    rw [div_le_div_iff_of_pos_right hk0]
    exact_mod_cast Nat.le_succ j
  have hmono : ∀ y ∈ Set.Icc (((j:ℕ):ℝ)/k) (((j+1:ℕ):ℝ)/k), g (((j:ℕ):ℝ)/k) ≤ g y := by
    intro y hy
    have hsub := subinterval_subset k j hk hj
    rw [Set.uIcc_of_le (by rw [hcast j] at hle; exact hle)] at hsub
    refine hg (pt_mem k j hk (by omega)) (hsub ?_) hy.1
    exact ⟨hy.1, by rw [← hcast j]; exact hy.2⟩
  calc g ((j:ℝ)/k) / k
      = ∫ _t in (((j:ℕ):ℝ)/k)..(((j+1:ℕ):ℝ)/k), g (((j:ℕ):ℝ)/k) := by
        rw [intervalIntegral.integral_const, hcast j]
        simp only [smul_eq_mul]
        field_simp
        ring
    _ ≤ ∫ t in (((j:ℕ):ℝ)/k)..(((j+1:ℕ):ℝ)/k), g t :=
        intervalIntegral.integral_mono_on hle intervalIntegrable_const (hint j hj) hmono

/-- The empirical average is at most the upper bin sum. -/
lemma average_le_upper (x : ℕ → ℝ) (g : ℝ → ℝ) (hg : MonotoneOn g (Set.Icc (0:ℝ) 1))
    (N k : ℕ) (hk : 0 < k) (hN : 0 < N) :
    (∑ n ∈ Finset.range N, g (Int.fract (x n))) / N
      ≤ ∑ j ∈ Finset.range k,
          g (((j:ℝ)+1)/k) * (edf x N (((j:ℝ)+1)/k) - edf x N ((j:ℝ)/k)) := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have key : ∀ j ∈ Finset.range k,
      ∑ n ∈ bin x N k j, g (Int.fract (x n)) ≤ (bin x N k j).card * g (((j:ℝ)+1)/k) := by
    intro j hj
    simp only [Finset.mem_range] at hj
    have hpt : ((j:ℝ)+1)/k ∈ Set.Icc (0:ℝ) 1 := by
      have h := pt_mem k (j+1) hk hj
      rwa [show ((j+1:ℕ):ℝ)/k = ((j:ℝ)+1)/k by push_cast; ring] at h
    have hb : ∀ n ∈ bin x N k j, g (Int.fract (x n)) ≤ g (((j:ℝ)+1)/k) := by
      intro n hn
      simp only [bin, Finset.mem_filter] at hn
      have hfl : Int.fract (x n) < ((j:ℝ)+1)/k := hn.2.2
      exact hg ⟨Int.fract_nonneg _, le_trans hfl.le hpt.2⟩ hpt hfl.le
    calc ∑ n ∈ bin x N k j, g (Int.fract (x n))
        ≤ ∑ _n ∈ bin x N k j, g (((j:ℝ)+1)/k) := Finset.sum_le_sum hb
      _ = (bin x N k j).card * g (((j:ℝ)+1)/k) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hRHS : ∑ j ∈ Finset.range k,
      g (((j:ℝ)+1)/k) * (edf x N (((j:ℝ)+1)/k) - edf x N ((j:ℝ)/k))
      = (∑ j ∈ Finset.range k, ((bin x N k j).card : ℝ) * g (((j:ℝ)+1)/k)) / N := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [edf, edf, ← sub_div, ← card_bin x N k j hk]
    ring
  rw [hRHS, ← sum_bin x g N k hk, div_le_div_iff_of_pos_right hN0]
  exact Finset.sum_le_sum key

/-- The empirical average is at least the lower bin sum. -/
lemma lower_le_average (x : ℕ → ℝ) (g : ℝ → ℝ) (hg : MonotoneOn g (Set.Icc (0:ℝ) 1))
    (N k : ℕ) (hk : 0 < k) (hN : 0 < N) :
    ∑ j ∈ Finset.range k,
        g ((j:ℝ)/k) * (edf x N (((j:ℝ)+1)/k) - edf x N ((j:ℝ)/k))
      ≤ (∑ n ∈ Finset.range N, g (Int.fract (x n))) / N := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have key : ∀ j ∈ Finset.range k,
      ((bin x N k j).card : ℝ) * g ((j:ℝ)/k) ≤ ∑ n ∈ bin x N k j, g (Int.fract (x n)) := by
    intro j hj
    simp only [Finset.mem_range] at hj
    have hpt : ((j:ℝ)/k) ∈ Set.Icc (0:ℝ) 1 := pt_mem k j hk (by omega)
    have hpt' : ((j:ℝ)+1)/k ∈ Set.Icc (0:ℝ) 1 := by
      have h := pt_mem k (j+1) hk hj
      rwa [show ((j+1:ℕ):ℝ)/k = ((j:ℝ)+1)/k by push_cast; ring] at h
    have hb : ∀ n ∈ bin x N k j, g ((j:ℝ)/k) ≤ g (Int.fract (x n)) := by
      intro n hn
      simp only [bin, Finset.mem_filter] at hn
      exact hg hpt ⟨Int.fract_nonneg _, le_trans hn.2.2.le hpt'.2⟩ hn.2.1
    calc ((bin x N k j).card : ℝ) * g ((j:ℝ)/k)
        = ∑ _n ∈ bin x N k j, g ((j:ℝ)/k) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ n ∈ bin x N k j, g (Int.fract (x n)) := Finset.sum_le_sum hb
  have hLHS : ∑ j ∈ Finset.range k,
      g ((j:ℝ)/k) * (edf x N (((j:ℝ)+1)/k) - edf x N ((j:ℝ)/k))
      = (∑ j ∈ Finset.range k, ((bin x N k j).card : ℝ) * g ((j:ℝ)/k)) / N := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [edf, edf, ← sub_div, ← card_bin x N k j hk]
    ring
  rw [hLHS, ← sum_bin x g N k hk, div_le_div_iff_of_pos_right hN0]
  exact Finset.sum_le_sum key

/-- Convergence of the upper bin sums. -/
lemma tendsto_upper (x : ℕ → ℝ) (hx : UniformlyDistributedMod1 x) (g : ℝ → ℝ) (k : ℕ)
    (hk : 0 < k) :
    Tendsto (fun N => ∑ j ∈ Finset.range k,
        g (((j:ℝ)+1)/k) * (edf x N (((j:ℝ)+1)/k) - edf x N ((j:ℝ)/k))) atTop
      (nhds (∑ j ∈ Finset.range k, g (((j:ℝ)+1)/k) / k)) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  refine tendsto_finset_sum _ ?_
  intro j hj
  simp only [Finset.mem_range] at hj
  have h1 : ((j:ℝ)+1)/k ∈ Set.Icc (0:ℝ) 1 := by
    have h := pt_mem k (j+1) hk hj
    rwa [show ((j+1:ℕ):ℝ)/k = ((j:ℝ)+1)/k by push_cast; ring] at h
  have h2 : ((j:ℝ)/k) ∈ Set.Icc (0:ℝ) 1 := pt_mem k j hk (by omega)
  have hconv := ((hx _ h1).sub (hx _ h2)).const_mul (g (((j:ℝ)+1)/k))
  have heq : g (((j:ℝ)+1)/k) * (((j:ℝ)+1)/k - (j:ℝ)/k) = g (((j:ℝ)+1)/k) / k := by
    field_simp
    ring
  rwa [heq] at hconv

/-- Convergence of the lower bin sums. -/
lemma tendsto_lower (x : ℕ → ℝ) (hx : UniformlyDistributedMod1 x) (g : ℝ → ℝ) (k : ℕ)
    (hk : 0 < k) :
    Tendsto (fun N => ∑ j ∈ Finset.range k,
        g ((j:ℝ)/k) * (edf x N (((j:ℝ)+1)/k) - edf x N ((j:ℝ)/k))) atTop
      (nhds (∑ j ∈ Finset.range k, g ((j:ℝ)/k) / k)) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  refine tendsto_finset_sum _ ?_
  intro j hj
  simp only [Finset.mem_range] at hj
  have h1 : ((j:ℝ)+1)/k ∈ Set.Icc (0:ℝ) 1 := by
    have h := pt_mem k (j+1) hk hj
    rwa [show ((j+1:ℕ):ℝ)/k = ((j:ℝ)+1)/k by push_cast; ring] at h
  have h2 : ((j:ℝ)/k) ∈ Set.Icc (0:ℝ) 1 := pt_mem k j hk (by omega)
  have hconv := ((hx _ h1).sub (hx _ h2)).const_mul (g ((j:ℝ)/k))
  have heq : g ((j:ℝ)/k) * (((j:ℝ)+1)/k - (j:ℝ)/k) = g ((j:ℝ)/k) / k := by
    field_simp
    ring
  rwa [heq] at hconv

/-- Equidistribution test for monotone functions. -/
theorem tendsto_average_of_monotoneOn (x : ℕ → ℝ) (hx : UniformlyDistributedMod1 x)
    (g : ℝ → ℝ) (hg : MonotoneOn g (Set.Icc (0:ℝ) 1)) :
    Tendsto (fun N => (∑ n ∈ Finset.range N, g (Int.fract (x n))) / N) atTop
      (nhds (∫ t in (0:ℝ)..1, g t)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hM : (0:ℝ) ≤ g 1 - g 0 := by
    have h01 : g 0 ≤ g 1 :=
      hg (by norm_num) (by norm_num) (by norm_num)
    linarith
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt (2 * (g 1 - g 0 + 1) / ε)
  set k : ℕ := k₀ + 1 with hkdef
  have hk : 0 < k := Nat.succ_pos _
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hkbig : 2 * (g 1 - g 0 + 1) / ε < k := by
    have : (k₀:ℝ) < k := by rw [hkdef]; push_cast; linarith
    linarith
  have hMk : (g 1 - g 0)/k < ε/2 := by
    rw [div_lt_iff₀ hk0]
    have h1 : 2 * (g 1 - g 0 + 1) < ε * k := by
      rw [div_lt_iff₀ hε] at hkbig
      linarith
    nlinarith
  have htel : (∑ j ∈ Finset.range k, g (((j:ℝ)+1)/k) / k)
      - (∑ j ∈ Finset.range k, g ((j:ℝ)/k) / k) = (g 1 - g 0)/k := by
    have hcongr : ∀ j ∈ Finset.range k, g (((j:ℝ)+1)/k)/k - g ((j:ℝ)/k)/k
        = (fun i : ℕ => g ((i:ℝ)/k)/k) (j+1) - (fun i : ℕ => g ((i:ℝ)/k)/k) j := by
      intro j _
      simp only
      push_cast
      ring
    have hsr : ∑ i ∈ Finset.range k,
        ((fun n : ℕ => g ((n:ℝ)/k)/k) (i+1) - (fun n : ℕ => g ((n:ℝ)/k)/k) i)
        = (fun n : ℕ => g ((n:ℝ)/k)/k) k - (fun n : ℕ => g ((n:ℝ)/k)/k) 0 :=
      Finset.sum_range_sub (fun n : ℕ => g ((n:ℝ)/k)/k) k
    rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl hcongr, hsr]
    simp only
    rw [div_self (ne_of_gt hk0)]
    norm_num
    ring
  have hUp := tendsto_upper x hx g k hk
  have hLo := tendsto_lower x hx g k hk
  rw [Metric.tendsto_atTop] at hUp hLo
  obtain ⟨N₁, hN₁⟩ := hUp (ε/2) (by linarith)
  obtain ⟨N₂, hN₂⟩ := hLo (ε/2) (by linarith)
  refine ⟨max 1 (max N₁ N₂), ?_⟩
  intro N hN
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one (le_trans (le_max_left _ _) hN)
  have h1 := hN₁ N (le_trans (le_trans (le_max_left N₁ N₂) (le_max_right 1 _)) hN)
  have h2 := hN₂ N (le_trans (le_trans (le_max_right N₁ N₂) (le_max_right 1 _)) hN)
  rw [Real.dist_eq, abs_lt] at h1 h2
  have hupper := average_le_upper x g hg N k hk hN0
  have hlower := lower_le_average x g hg N k hk hN0
  have hRint := integral_le_upper_sum g hg k hk
  have hLint := lower_sum_le_integral g hg k hk
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **Equidistribution test for functions of bounded variation.**

If `x : ℕ → ℝ` is uniformly distributed mod one (i.e. the empirical distribution functions of
its fractional parts converge pointwise on `[0,1]` to the uniform distribution function), then
for every function `f` of bounded variation on `[0,1]` the Birkhoff averages of `f` along the
fractional parts of `x` converge to the integral of `f` over `[0,1]`. -/
theorem equidistribution_of_BV_uniform (x : ℕ → ℝ) (hx : UniformlyDistributedMod1 x)
    (f : ℝ → ℝ) (hf : BoundedVariationOn f (Set.Icc (0:ℝ) 1)) :
    Tendsto (fun N => (∑ n ∈ Finset.range N, f (Int.fract (x n))) / N) atTop
      (nhds (∫ t in (0:ℝ)..1, f t)) := by
  obtain ⟨p, q, hp, hq, hpq⟩ :=
    hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  have huIcc : Set.uIcc (0:ℝ) 1 = Set.Icc (0:ℝ) 1 := Set.uIcc_of_le (by norm_num)
  have hpi : IntervalIntegrable p MeasureTheory.volume 0 1 :=
    MonotoneOn.intervalIntegrable (by rw [huIcc]; exact hp)
  have hqi : IntervalIntegrable q MeasureTheory.volume 0 1 :=
    MonotoneOn.intervalIntegrable (by rw [huIcc]; exact hq)
  have hI : (∫ t in (0:ℝ)..1, f t)
      = (∫ t in (0:ℝ)..1, p t) - (∫ t in (0:ℝ)..1, q t) := by
    rw [hpq]
    simpa using intervalIntegral.integral_sub hpi hqi
  have hsum : ∀ N : ℕ, (∑ n ∈ Finset.range N, f (Int.fract (x n))) / N
      = (∑ n ∈ Finset.range N, p (Int.fract (x n))) / N
        - (∑ n ∈ Finset.range N, q (Int.fract (x n))) / N := by
    intro N
    rw [hpq]
    simp only [Pi.sub_apply, Finset.sum_sub_distrib]
    ring
  have hlim := (tendsto_average_of_monotoneOn x hx p hp).sub
    (tendsto_average_of_monotoneOn x hx q hq)
  rw [hI]
  exact hlim.congr (fun N => (hsum N).symm)

end Brockian.EquidistributionBVReduction

