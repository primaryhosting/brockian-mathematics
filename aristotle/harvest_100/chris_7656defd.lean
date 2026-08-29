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

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.EquidistributionBVReduction

open Filter Set MeasureTheory

/-- `configCount x S N` is the number of indices `n < N` whose fractional part
`Int.fract (x n)` lands in the "configuration window" `S`. -/
noncomputable def configCount (x : ℕ → ℝ) (S : Set ℝ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun n => Int.fract (x n) ∈ S).card

/-- The sequence `x` is equidistributed modulo one: for every subinterval
`[a, b) ⊆ [0, 1]`, the density of indices whose fractional part lies in `[a, b)`
is the length `b - a`. -/
def EquidistributedMod1 (x : ℕ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
    Tendsto (fun N : ℕ => (configCount x (Set.Ico a b) N : ℝ) / N) atTop (nhds (b - a))

/-- The Cesàro average of `f` along the fractional parts of the first `N` terms of `x`. -/
noncomputable def configAvg (x : ℕ → ℝ) (f : ℝ → ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.range N, f (Int.fract (x n))) / N

/-- Clamping to the unit interval. -/
noncomputable def clamp01 (t : ℝ) : ℝ := max 0 (min 1 t)

lemma clamp01_mem (t : ℝ) : clamp01 t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

lemma clamp01_monotone : Monotone clamp01 := fun _ _ h => by
  unfold clamp01
  exact max_le_max le_rfl (min_le_min le_rfl h)

lemma clamp01_eq_self {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : clamp01 t = t := by
  obtain ⟨h0, h1⟩ := ht
  unfold clamp01
  rw [min_eq_right h1, max_eq_right h0]

/-- Monotone extension of a function that is monotone on `[0,1]`. -/
noncomputable def monoExt (g : ℝ → ℝ) : ℝ → ℝ := fun t => g (clamp01 t)

lemma monoExt_monotone {g : ℝ → ℝ} (hg : MonotoneOn g (Set.Icc (0 : ℝ) 1)) :
    Monotone (monoExt g) := fun _ _ h =>
  hg (clamp01_mem _) (clamp01_mem _) (clamp01_monotone h)

lemma monoExt_eq {g : ℝ → ℝ} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : monoExt g t = g t := by
  simp [monoExt, clamp01_eq_self ht]

lemma fract_mem_Icc (t : ℝ) : Int.fract t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩

/-! ### Riemann-sum machinery for a globally monotone function -/

section MonotoneCase

variable (x : ℕ → ℝ)

/-- The lower Riemann sum of `G` for the uniform partition of `[0,1]` into `k` pieces. -/
noncomputable def lowerSum (G : ℝ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, G ((i : ℝ) / k) / k

/-- The upper Riemann sum of `G` for the uniform partition of `[0,1]` into `k` pieces. -/
noncomputable def upperSum (G : ℝ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, G (((i : ℝ) + 1) / k) / k

lemma floor_eq_iff_mem_Ico {t : ℝ} (ht : 0 ≤ t) {i k : ℕ} (hk : 0 < k) :
    ⌊t * k⌋₊ = i ↔ t ∈ Set.Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  rw [Nat.floor_eq_iff (by positivity)]
  rw [Set.mem_Ico, div_le_iff₀ hkpos, lt_div_iff₀ hkpos]

lemma configCount_Ico_eq_card (i k N : ℕ) :
    (configCount x (Set.Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)) N) =
      ((Finset.range N).filter fun n =>
        Int.fract (x n) ∈ Set.Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)).card := by
  simp [configCount]

lemma filter_fiber_eq (k N : ℕ) (hk : 0 < k) (i : ℕ) :
    ((Finset.range N).filter fun n => ⌊Int.fract (x n) * k⌋₊ = i) =
      ((Finset.range N).filter fun n =>
        Int.fract (x n) ∈ Set.Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)) := by
  apply Finset.filter_congr
  intro n _
  exact floor_eq_iff_mem_Ico (Int.fract_nonneg _) hk

lemma sum_fiberwise (G : ℝ → ℝ) (k N : ℕ) (hk : 0 < k) :
    ∑ n ∈ Finset.range N, G (Int.fract (x n)) =
      ∑ i ∈ Finset.range k, ∑ n ∈ ((Finset.range N).filter fun n =>
        Int.fract (x n) ∈ Set.Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)),
          G (Int.fract (x n)) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hmaps : ∀ n ∈ Finset.range N, ⌊Int.fract (x n) * k⌋₊ ∈ Finset.range k := by
    intro n _
    have h1 : Int.fract (x n) * k < k := by
      nlinarith [Int.fract_lt_one (x n), Int.fract_nonneg (x n)]
    simp only [Finset.mem_range]
    exact (Nat.floor_lt (mul_nonneg (Int.fract_nonneg _) hkpos.le)).2 (by exact_mod_cast h1)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  exact Finset.sum_congr rfl fun i _ => by rw [filter_fiber_eq x k N hk i]

lemma lower_le_sum (G : ℝ → ℝ) (hG : Monotone G) (k N : ℕ) (hk : 0 < k) :
    (∑ i ∈ Finset.range k,
        G ((i : ℝ) / k) * (configCount x (Set.Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)) N : ℝ)) ≤
      ∑ n ∈ Finset.range N, G (Int.fract (x n)) := by
  rw [sum_fiberwise x G k N hk]
  simp only [configCount_Ico_eq_card]
  refine Finset.sum_le_sum fun i _ => ?_
  have hb : ∀ n ∈ ((Finset.range N).filter fun n =>
      Int.fract (x n) ∈ Set.Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)),
      G ((i : ℝ) / k) ≤ G (Int.fract (x n)) := by
    intro n hn
    simp only [Finset.mem_filter, Set.mem_Ico] at hn
    exact hG hn.2.1
  have h2 := Finset.card_nsmul_le_sum _ _ _ hb
  rw [nsmul_eq_mul, mul_comm] at h2
  exact h2

lemma sum_le_upper (G : ℝ → ℝ) (hG : Monotone G) (k N : ℕ) (hk : 0 < k) :
    ∑ n ∈ Finset.range N, G (Int.fract (x n)) ≤
      ∑ i ∈ Finset.range k,
        G (((i : ℝ) + 1) / k) *
          (configCount x (Set.Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)) N : ℝ) := by
  rw [sum_fiberwise x G k N hk]
  simp only [configCount_Ico_eq_card]
  refine Finset.sum_le_sum fun i _ => ?_
  have hb : ∀ n ∈ ((Finset.range N).filter fun n =>
      Int.fract (x n) ∈ Set.Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)),
      G (Int.fract (x n)) ≤ G (((i : ℝ) + 1) / k) := by
    intro n hn
    simp only [Finset.mem_filter, Set.mem_Ico] at hn
    exact hG hn.2.2.le
  have h2 := Finset.sum_le_card_nsmul _ _ _ hb
  rw [nsmul_eq_mul, mul_comm] at h2
  exact h2

lemma tendsto_configCount_div (hx : EquidistributedMod1 x) (k i : ℕ) (hk : 0 < k)
    (hik : i < k) :
    Tendsto (fun N : ℕ =>
      (configCount x (Set.Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)) N : ℝ) / N) atTop
      (nhds (1 / k)) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have h0 : (0 : ℝ) ≤ (i : ℝ) / k := by positivity
  have hsplit : ((i : ℝ) + 1) / k = (i : ℝ) / k + 1 / k := by ring
  have h1k : (0 : ℝ) < 1 / k := by positivity
  have hab : (i : ℝ) / k ≤ ((i : ℝ) + 1) / k := by rw [hsplit]; linarith
  have hb1 : ((i : ℝ) + 1) / k ≤ 1 := by
    rw [div_le_one hkpos]
    have : (i : ℝ) + 1 ≤ k := by exact_mod_cast hik
    linarith
  have h := hx ((i : ℝ) / k) (((i : ℝ) + 1) / k) h0 hab hb1
  have heq : ((i : ℝ) + 1) / k - (i : ℝ) / k = 1 / k := by rw [hsplit]; ring
  rwa [heq] at h

lemma tendsto_lowerSum (hx : EquidistributedMod1 x) (G : ℝ → ℝ) (k : ℕ) (hk : 0 < k) :
    Tendsto (fun N : ℕ =>
      (∑ i ∈ Finset.range k,
        G ((i : ℝ) / k) *
          (configCount x (Set.Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)) N : ℝ)) / N)
      atTop (nhds (lowerSum G k)) := by
  have hfun : ∀ N : ℕ,
      (∑ i ∈ Finset.range k,
        G ((i : ℝ) / k) *
          (configCount x (Set.Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)) N : ℝ)) / N =
      ∑ i ∈ Finset.range k,
        G ((i : ℝ) / k) *
          ((configCount x (Set.Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)) N : ℝ) / N) := by
    intro N
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [hfun]
  have hlim : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range k,
      G ((i : ℝ) / k) *
        ((configCount x (Set.Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)) N : ℝ) / N))
      atTop (nhds (∑ i ∈ Finset.range k, G ((i : ℝ) / k) * (1 / k))) := by
    refine tendsto_finset_sum _ fun i hi => ?_
    exact tendsto_const_nhds.mul
      (tendsto_configCount_div x hx k i hk (Finset.mem_range.mp hi))
  have : (∑ i ∈ Finset.range k, G ((i : ℝ) / k) * (1 / k)) = lowerSum G k := by
    simp only [lowerSum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rwa [this] at hlim

lemma tendsto_upperSum (hx : EquidistributedMod1 x) (G : ℝ → ℝ) (k : ℕ) (hk : 0 < k) :
    Tendsto (fun N : ℕ =>
      (∑ i ∈ Finset.range k,
        G (((i : ℝ) + 1) / k) *
          (configCount x (Set.Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)) N : ℝ)) / N)
      atTop (nhds (upperSum G k)) := by
  have hfun : ∀ N : ℕ,
      (∑ i ∈ Finset.range k,
        G (((i : ℝ) + 1) / k) *
          (configCount x (Set.Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)) N : ℝ)) / N =
      ∑ i ∈ Finset.range k,
        G (((i : ℝ) + 1) / k) *
          ((configCount x (Set.Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)) N : ℝ) / N) := by
    intro N
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [hfun]
  have hlim : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range k,
      G (((i : ℝ) + 1) / k) *
        ((configCount x (Set.Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)) N : ℝ) / N))
      atTop (nhds (∑ i ∈ Finset.range k, G (((i : ℝ) + 1) / k) * (1 / k))) := by
    refine tendsto_finset_sum _ fun i hi => ?_
    exact tendsto_const_nhds.mul
      (tendsto_configCount_div x hx k i hk (Finset.mem_range.mp hi))
  have : (∑ i ∈ Finset.range k, G (((i : ℝ) + 1) / k) * (1 / k)) = upperSum G k := by
    simp only [upperSum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rwa [this] at hlim

lemma div_le_div_succ (i k : ℕ) (hk : 0 < k) : (i : ℝ) / k ≤ ((i : ℝ) + 1) / k := by
  have h1k : (0 : ℝ) < 1 / k := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    positivity
  have hsplit : ((i : ℝ) + 1) / k = (i : ℝ) / k + 1 / k := by ring
  rw [hsplit]; linarith

lemma sum_integral_partition (G : ℝ → ℝ) (hG : Monotone G) (k : ℕ) (hk : 0 < k) :
    ∑ i ∈ Finset.range k, ∫ t in ((i : ℝ) / k)..(((i : ℝ) + 1) / k), G t =
      ∫ t in (0 : ℝ)..1, G t := by
  have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have h := intervalIntegral.sum_integral_adjacent_intervals
    (μ := MeasureTheory.volume) (a := fun i : ℕ => (i : ℝ) / k) (f := G) (n := k)
    (fun i _ => hG.intervalIntegrable)
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div] at h
  rw [div_self hkne] at h
  exact h

lemma lowerSum_le_integral (G : ℝ → ℝ) (hG : Monotone G) (k : ℕ) (hk : 0 < k) :
    lowerSum G k ≤ ∫ t in (0 : ℝ)..1, G t := by
  rw [← sum_integral_partition G hG k hk]
  refine Finset.sum_le_sum fun i _ => ?_
  have hle := div_le_div_succ i k hk
  have hmono := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hle
    intervalIntegrable_const hG.intervalIntegrable
    (fun t ht => hG ht.1)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hval : (((i : ℝ) + 1) / k - (i : ℝ) / k) * G ((i : ℝ) / k) = G ((i : ℝ) / k) / k := by
    have : ((i : ℝ) + 1) / k - (i : ℝ) / k = 1 / k := by ring
    rw [this]; ring
  rw [hval] at hmono
  exact hmono

lemma integral_le_upperSum (G : ℝ → ℝ) (hG : Monotone G) (k : ℕ) (hk : 0 < k) :
    (∫ t in (0 : ℝ)..1, G t) ≤ upperSum G k := by
  rw [← sum_integral_partition G hG k hk]
  refine Finset.sum_le_sum fun i _ => ?_
  have hle := div_le_div_succ i k hk
  have hmono := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hle
    hG.intervalIntegrable intervalIntegrable_const
    (fun t ht => hG ht.2)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hval : (((i : ℝ) + 1) / k - (i : ℝ) / k) * G (((i : ℝ) + 1) / k)
      = G (((i : ℝ) + 1) / k) / k := by
    have : ((i : ℝ) + 1) / k - (i : ℝ) / k = 1 / k := by ring
    rw [this]; ring
  rw [hval] at hmono
  exact hmono

lemma upperSum_sub_lowerSum (G : ℝ → ℝ) (k : ℕ) (hk : 0 < k) :
    upperSum G k - lowerSum G k = (G 1 - G 0) / k := by
  have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have h1 : upperSum G k = ∑ i ∈ Finset.range k, G (((i + 1 : ℕ) : ℝ) / k) / k := by
    simp only [upperSum]
    exact Finset.sum_congr rfl fun i _ => by push_cast; ring_nf
  have h2 : lowerSum G k = ∑ i ∈ Finset.range k, G (((i : ℕ) : ℝ) / k) / k := rfl
  rw [h1, h2, ← Finset.sum_sub_distrib]
  have h3 : ∑ i ∈ Finset.range k,
      (G (((i + 1 : ℕ) : ℝ) / k) / k - G (((i : ℕ) : ℝ) / k) / k)
      = (∑ i ∈ Finset.range k,
          (G (((i + 1 : ℕ) : ℝ) / k) - G (((i : ℕ) : ℝ) / k))) / k := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h3, Finset.sum_range_sub (fun j : ℕ => G ((j : ℝ) / k)), div_self hkne, Nat.cast_zero,
    zero_div]

/-- The Cesàro averages of a monotone function along an equidistributed sequence
converge to its integral over `[0,1]`. -/
theorem configAvg_tendsto_of_monotone (hx : EquidistributedMod1 x) (G : ℝ → ℝ)
    (hG : Monotone G) :
    Tendsto (configAvg x G) atTop (nhds (∫ t in (0 : ℝ)..1, G t)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk1, hk2⟩ : ∃ k : ℕ, 0 < k ∧ (G 1 - G 0) / k < ε / 2 := by
    obtain ⟨k, hk⟩ := exists_nat_gt (max 1 ((G 1 - G 0) * 2 / ε))
    have hk1 : (1 : ℝ) < k := lt_of_le_of_lt (le_max_left _ _) hk
    have hkpos : (0 : ℝ) < k := by linarith
    refine ⟨k, by exact_mod_cast hkpos, ?_⟩
    rw [div_lt_iff₀ hkpos]
    have h' : (G 1 - G 0) * 2 / ε < k := lt_of_le_of_lt (le_max_right _ _) hk
    rw [div_lt_iff₀ hε] at h'
    linarith
  have hlow := tendsto_lowerSum x hx G k hk1
  have hup := tendsto_upperSum x hx G k hk1
  rw [Metric.tendsto_atTop] at hlow hup
  obtain ⟨N1, hN1⟩ := hlow (ε / 4) (by linarith)
  obtain ⟨N2, hN2⟩ := hup (ε / 4) (by linarith)
  refine ⟨max 1 (max N1 N2), fun N hN => ?_⟩
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one (le_trans (le_max_left _ _) hN)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have h1 := hN1 N (le_trans (le_trans (le_max_left _ _) (le_max_right 1 _)) hN)
  have h2 := hN2 N (le_trans (le_trans (le_max_right _ _) (le_max_right 1 _)) hN)
  rw [Real.dist_eq, abs_lt] at h1 h2
  have hlowle : (∑ i ∈ Finset.range k,
      G ((i : ℝ) / k) *
        (configCount x (Set.Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)) N : ℝ)) / N ≤
      configAvg x G N := by
    rw [configAvg]
    gcongr
    exact lower_le_sum x G hG k N hk1
  have hupge : configAvg x G N ≤ (∑ i ∈ Finset.range k,
      G (((i : ℝ) + 1) / k) *
        (configCount x (Set.Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)) N : ℝ)) / N := by
    rw [configAvg]
    gcongr
    exact sum_le_upper x G hG k N hk1
  have hLI := lowerSum_le_integral G hG k hk1
  have hIU := integral_le_upperSum G hG k hk1
  have hUL := upperSum_sub_lowerSum G k hk1
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end MonotoneCase

/-- **Config-count density from bounded variation.**  If `x` is equidistributed modulo
one and `f` has bounded variation on `[0,1]`, then the Cesàro averages of `f` along the
fractional parts of `x` converge to the integral of `f` over `[0,1]`. -/
theorem configCount_density_of_BV (x : ℕ → ℝ) (hx : EquidistributedMod1 x) (f : ℝ → ℝ)
    (hf : BoundedVariationOn f (Set.Icc (0 : ℝ) 1)) :
    Tendsto (configAvg x f) atTop (nhds (∫ t in (0 : ℝ)..1, f t)) := by
  obtain ⟨p, q, hp, hq, rfl⟩ :=
    hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  have hP : Monotone (monoExt p) := monoExt_monotone hp
  have hQ : Monotone (monoExt q) := monoExt_monotone hq
  have havg : ∀ N : ℕ,
      configAvg x (p - q) N = configAvg x (monoExt p) N - configAvg x (monoExt q) N := by
    intro N
    simp only [configAvg, ← sub_div]
    congr 1
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [monoExt_eq (fract_mem_Icc _), monoExt_eq (fract_mem_Icc _)]
    rfl
  have hint : (∫ t in (0 : ℝ)..1, (p - q) t)
      = (∫ t in (0 : ℝ)..1, monoExt p t) - ∫ t in (0 : ℝ)..1, monoExt q t := by
    have hcong : (∫ t in (0 : ℝ)..1, (p - q) t)
        = ∫ t in (0 : ℝ)..1, (monoExt p t - monoExt q t) := by
      refine intervalIntegral.integral_congr ?_
      intro t ht
      rw [Set.uIcc_of_le zero_le_one] at ht
      show (p - q) t = monoExt p t - monoExt q t
      rw [monoExt_eq ht, monoExt_eq ht]
      rfl
    rw [hcong, intervalIntegral.integral_sub hP.intervalIntegrable hQ.intervalIntegrable]
  rw [funext havg, hint]
  exact (configAvg_tendsto_of_monotone x hx _ hP).sub
    (configAvg_tendsto_of_monotone x hx _ hQ)

end Brockian.EquidistributionBVReduction

