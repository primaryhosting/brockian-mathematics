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

/-
# Total Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.total_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open Filter Topology
open scoped BigOperators Classical

namespace Brockian
namespace EquidistributionBVReduction

/-- The number of indices `n < N` whose fractional part `Int.fract (x n)` lies in `[a, b)`. -/
noncomputable def countIco (x : ℕ → ℝ) (a b : ℝ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico a b).card

/-- A sequence `x` is equidistributed mod 1 if the proportion of the first `N` terms whose
fractional part lies in a subinterval `[a,b) ⊆ [0,1]` tends to the length `b - a`. -/
def EquidistributedMod1 (x : ℕ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
    Tendsto (fun N : ℕ => (countIco x a b N : ℝ) / N) atTop (𝓝 (b - a))

/-- Jordan decomposition form of "bounded variation": `g` is a difference of two monotone
functions. -/
def IsBVJordan (g : ℝ → ℝ) : Prop :=
  ∃ g₁ g₂ : ℝ → ℝ, Monotone g₁ ∧ Monotone g₂ ∧ ∀ y, g y = g₁ y - g₂ y

/-- The total (Weyl) sum `∑_{n<N} g (fract (x n))`. -/
noncomputable def total (g : ℝ → ℝ) (x : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, g (Int.fract (x n))

/-- The main term `N * ∫₀¹ g`. -/
noncomputable def main (g : ℝ → ℝ) (N : ℕ) : ℝ := (N : ℝ) * ∫ t in (0:ℝ)..1, g t

section Partition

variable {m : ℕ} {y : ℝ}

lemma countIco_eq_sum (x : ℕ → ℝ) (a b : ℝ) (N : ℕ) :
    (countIco x a b N : ℝ)
      = ∑ n ∈ Finset.range N, (if Int.fract (x n) ∈ Set.Ico a b then (1:ℝ) else 0) := by
  rw [countIco, Finset.sum_boole]

lemma mem_Ico_iff_floor (hm : 0 < m) (hy : 0 ≤ y) (i : ℕ) :
    y ∈ Set.Ico ((i : ℝ) / m) (((i : ℝ) + 1) / m) ↔ ⌊y * m⌋₊ = i := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  rw [Nat.floor_eq_iff (by positivity)]
  rw [Set.mem_Ico, div_le_iff₀ hm', lt_div_iff₀ hm']

lemma sum_indicator_eq_one (hm : 0 < m) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    ∑ i ∈ Finset.range m,
        (if y ∈ Set.Ico ((i : ℝ) / m) (((i : ℝ) + 1) / m) then (1 : ℝ) else 0) = 1 := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hlt : ⌊y * m⌋₊ < m := by
    apply Nat.floor_lt' (by omega) |>.mpr
    calc y * m < 1 * m := by nlinarith
      _ = m := by ring
  have hcongr : ∀ i ∈ Finset.range m,
      (if y ∈ Set.Ico ((i : ℝ) / m) (((i : ℝ) + 1) / m) then (1 : ℝ) else 0)
        = (if ⌊y * m⌋₊ = i then (1:ℝ) else 0) := by
    intro i _
    simp only [mem_Ico_iff_floor hm hy0 i]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq]
  simp [Finset.mem_range, hlt]

end Partition

section Sandwich

variable {g : ℝ → ℝ} {x : ℕ → ℝ} {m N : ℕ}

/-- Lower step-function bound for the total sum. -/
lemma sum_le_total (hg : Monotone g) (hm : 0 < m) :
    ∑ i ∈ Finset.range m,
        g ((i : ℝ) / m) * (countIco x ((i : ℝ) / m) (((i : ℝ) + 1) / m) N : ℝ)
      ≤ total g x N := by
  have step : ∀ i ∈ Finset.range m,
      g ((i : ℝ) / m) * (countIco x ((i : ℝ) / m) (((i : ℝ) + 1) / m) N : ℝ)
        = ∑ n ∈ Finset.range N,
            (if Int.fract (x n) ∈ Set.Ico ((i:ℝ)/m) (((i:ℝ)+1)/m) then g ((i:ℝ)/m) else 0) := by
    intro i _
    rw [countIco_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    split <;> ring
  rw [Finset.sum_congr rfl step, Finset.sum_comm]
  refine Finset.sum_le_sum fun n _ => ?_
  set y := Int.fract (x n) with hy
  have hy0 : 0 ≤ y := Int.fract_nonneg _
  have hy1 : y < 1 := Int.fract_lt_one _
  have hbound : ∀ i ∈ Finset.range m,
      (if y ∈ Set.Ico ((i:ℝ)/m) (((i:ℝ)+1)/m) then g ((i:ℝ)/m) else 0)
        ≤ g y * (if y ∈ Set.Ico ((i:ℝ)/m) (((i:ℝ)+1)/m) then (1:ℝ) else 0) := by
    intro i _
    by_cases h : y ∈ Set.Ico ((i:ℝ)/m) (((i:ℝ)+1)/m)
    · simp [h, hg h.1]
    · simp [h]
  calc ∑ i ∈ Finset.range m,
        (if y ∈ Set.Ico ((i:ℝ)/m) (((i:ℝ)+1)/m) then g ((i:ℝ)/m) else 0)
      ≤ ∑ i ∈ Finset.range m, g y * (if y ∈ Set.Ico ((i:ℝ)/m) (((i:ℝ)+1)/m) then (1:ℝ) else 0) :=
        Finset.sum_le_sum hbound
    _ = g y := by rw [← Finset.mul_sum, sum_indicator_eq_one hm hy0 hy1, mul_one]

/-- Upper step-function bound for the total sum. -/
lemma total_le_sum (hg : Monotone g) (hm : 0 < m) :
    total g x N
      ≤ ∑ i ∈ Finset.range m,
        g (((i : ℝ) + 1) / m) * (countIco x ((i : ℝ) / m) (((i : ℝ) + 1) / m) N : ℝ) := by
  have step : ∀ i ∈ Finset.range m,
      g (((i : ℝ) + 1) / m) * (countIco x ((i : ℝ) / m) (((i : ℝ) + 1) / m) N : ℝ)
        = ∑ n ∈ Finset.range N,
            (if Int.fract (x n) ∈ Set.Ico ((i:ℝ)/m) (((i:ℝ)+1)/m) then g (((i:ℝ)+1)/m)
              else 0) := by
    intro i _
    rw [countIco_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    split <;> ring
  rw [Finset.sum_congr rfl step, Finset.sum_comm]
  refine Finset.sum_le_sum fun n _ => ?_
  set y := Int.fract (x n) with hy
  have hy0 : 0 ≤ y := Int.fract_nonneg _
  have hy1 : y < 1 := Int.fract_lt_one _
  have hbound : ∀ i ∈ Finset.range m,
      g y * (if y ∈ Set.Ico ((i:ℝ)/m) (((i:ℝ)+1)/m) then (1:ℝ) else 0)
        ≤ (if y ∈ Set.Ico ((i:ℝ)/m) (((i:ℝ)+1)/m) then g (((i:ℝ)+1)/m) else 0) := by
    intro i _
    by_cases h : y ∈ Set.Ico ((i:ℝ)/m) (((i:ℝ)+1)/m)
    · simp [h, hg h.2.le]
    · simp [h]
  calc g y
      = ∑ i ∈ Finset.range m, g y * (if y ∈ Set.Ico ((i:ℝ)/m) (((i:ℝ)+1)/m) then (1:ℝ) else 0) :=
        by rw [← Finset.mul_sum, sum_indicator_eq_one hm hy0 hy1, mul_one]
    _ ≤ ∑ i ∈ Finset.range m,
          (if y ∈ Set.Ico ((i:ℝ)/m) (((i:ℝ)+1)/m) then g (((i:ℝ)+1)/m) else 0) :=
        Finset.sum_le_sum hbound

end Sandwich

section Riemann

variable {g : ℝ → ℝ} {m : ℕ}

lemma lower_riemann (hg : Monotone g) (hm : 0 < m) :
    ∑ i ∈ Finset.range m, g ((i : ℝ) / m) * (1 / m) ≤ ∫ t in (0:ℝ)..1, g t := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have key := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun i : ℕ => (i:ℝ)/m) (n := m) (f := g) (μ := MeasureTheory.volume)
    (fun k _ => hg.intervalIntegrable)
  simp only [Nat.cast_zero, zero_div, div_self (ne_of_gt hm')] at key
  push_cast at key
  rw [← key]
  refine Finset.sum_le_sum fun i _ => ?_
  have hle : (i:ℝ)/m ≤ ((i : ℝ) + 1)/m := by gcongr; linarith
  have heq : g ((i:ℝ)/m) * (1/m) = ∫ _u in ((i:ℝ)/m)..((i:ℝ)+1)/m, g ((i:ℝ)/m) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    field_simp
    ring
  rw [heq]
  exact intervalIntegral.integral_mono_on hle intervalIntegrable_const hg.intervalIntegrable
    (fun u hu => hg hu.1)

lemma upper_riemann (hg : Monotone g) (hm : 0 < m) :
    (∫ t in (0:ℝ)..1, g t) ≤ ∑ i ∈ Finset.range m, g (((i : ℝ) + 1) / m) * (1 / m) := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have key := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun i : ℕ => (i:ℝ)/m) (n := m) (f := g) (μ := MeasureTheory.volume)
    (fun k _ => hg.intervalIntegrable)
  simp only [Nat.cast_zero, zero_div, div_self (ne_of_gt hm')] at key
  push_cast at key
  rw [← key]
  refine Finset.sum_le_sum fun i _ => ?_
  have hle : (i:ℝ)/m ≤ ((i : ℝ) + 1)/m := by gcongr; linarith
  have heq : g (((i:ℝ)+1)/m) * (1/m) = ∫ _u in ((i:ℝ)/m)..((i:ℝ)+1)/m, g (((i:ℝ)+1)/m) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    field_simp
    ring
  rw [heq]
  exact intervalIntegral.integral_mono_on hle hg.intervalIntegrable intervalIntegrable_const
    (fun u hu => hg hu.2)

lemma riemann_gap (g : ℝ → ℝ) (hm : 0 < m) :
    ∑ i ∈ Finset.range m, g (((i : ℝ) + 1) / m) * (1 / m)
      - ∑ i ∈ Finset.range m, g ((i : ℝ) / m) * (1 / m) = (g 1 - g 0) / m := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  rw [← Finset.sum_sub_distrib]
  have key := Finset.sum_range_sub (fun i : ℕ => g ((i:ℝ)/m) * (1/m)) m
  have hcongr : ∀ i ∈ Finset.range m,
      g (((i : ℝ) + 1) / m) * (1 / m) - g ((i : ℝ) / m) * (1 / m)
        = (fun i : ℕ => g ((i:ℝ)/m) * (1/m)) (i+1) - (fun i : ℕ => g ((i:ℝ)/m) * (1/m)) i := by
    intro i _
    simp only
    push_cast
    ring
  rw [Finset.sum_congr rfl hcongr, key]
  simp only [Nat.cast_zero, zero_div, div_self (ne_of_gt hm')]
  ring

end Riemann

section Limits

variable {g : ℝ → ℝ} {x : ℕ → ℝ} {m : ℕ}

lemma tendsto_count_div (hx : EquidistributedMod1 x) (hm : 0 < m) {i : ℕ}
    (hi : i ∈ Finset.range m) :
    Tendsto (fun N : ℕ => (countIco x ((i : ℝ) / m) (((i : ℝ) + 1) / m) N : ℝ) / N)
      atTop (𝓝 (1 / m)) := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have him : (i : ℝ) + 1 ≤ m := by
    have : i + 1 ≤ m := Finset.mem_range.mp hi
    exact_mod_cast this
  have h := hx ((i : ℝ) / m) (((i : ℝ) + 1) / m) (by positivity)
    (by gcongr; linarith) (by rw [div_le_one hm']; exact him)
  have hdiff : ((i : ℝ) + 1) / m - (i : ℝ) / m = 1 / m := by
    field_simp
    ring
  rwa [hdiff] at h

/-- The lower step-function averages converge to the lower Riemann sum. -/
lemma tendsto_lo (hx : EquidistributedMod1 x) (hm : 0 < m) :
    Tendsto (fun N : ℕ => ∑ i ∈ Finset.range m,
        g ((i : ℝ) / m) * ((countIco x ((i : ℝ) / m) (((i : ℝ) + 1) / m) N : ℝ) / N))
      atTop (𝓝 (∑ i ∈ Finset.range m, g ((i : ℝ) / m) * (1 / m))) :=
  tendsto_finset_sum _ fun _ hi => (tendsto_count_div hx hm hi).const_mul _

/-- The upper step-function averages converge to the upper Riemann sum. -/
lemma tendsto_hi (hx : EquidistributedMod1 x) (hm : 0 < m) :
    Tendsto (fun N : ℕ => ∑ i ∈ Finset.range m,
        g (((i : ℝ) + 1) / m) * ((countIco x ((i : ℝ) / m) (((i : ℝ) + 1) / m) N : ℝ) / N))
      atTop (𝓝 (∑ i ∈ Finset.range m, g (((i : ℝ) + 1) / m) * (1 / m))) :=
  tendsto_finset_sum _ fun _ hi => (tendsto_count_div hx hm hi).const_mul _

lemma lo_le_avg (hg : Monotone g) (hm : 0 < m) (N : ℕ) :
    ∑ i ∈ Finset.range m,
        g ((i : ℝ) / m) * ((countIco x ((i : ℝ) / m) (((i : ℝ) + 1) / m) N : ℝ) / N)
      ≤ total g x N / N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [total, countIco]
  · have hN' : (0:ℝ) < N := by exact_mod_cast hN
    have hrw : ∑ i ∈ Finset.range m,
        g ((i : ℝ) / m) * ((countIco x ((i : ℝ) / m) (((i : ℝ) + 1) / m) N : ℝ) / N)
        = (∑ i ∈ Finset.range m,
            g ((i : ℝ) / m) * (countIco x ((i : ℝ) / m) (((i : ℝ) + 1) / m) N : ℝ)) / N := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_div_assoc]
    rw [hrw]
    gcongr
    exact sum_le_total hg hm

lemma avg_le_hi (hg : Monotone g) (hm : 0 < m) (N : ℕ) :
    total g x N / N
      ≤ ∑ i ∈ Finset.range m,
        g (((i : ℝ) + 1) / m) * ((countIco x ((i : ℝ) / m) (((i : ℝ) + 1) / m) N : ℝ) / N) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [total, countIco]
  · have hN' : (0:ℝ) < N := by exact_mod_cast hN
    have hrw : ∑ i ∈ Finset.range m,
        g (((i : ℝ) + 1) / m) * ((countIco x ((i : ℝ) / m) (((i : ℝ) + 1) / m) N : ℝ) / N)
        = (∑ i ∈ Finset.range m,
            g (((i : ℝ) + 1) / m) * (countIco x ((i : ℝ) / m) (((i : ℝ) + 1) / m) N : ℝ)) / N := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_div_assoc]
    rw [hrw]
    gcongr
    exact total_le_sum hg hm

end Limits

/-- **Equidistribution for monotone test functions**: if `x` is equidistributed mod 1 and `g`
is monotone, the averages `(1/N) ∑_{n<N} g (fract (x n))` converge to `∫₀¹ g`. -/
theorem monotone_average_tendsto {g : ℝ → ℝ} {x : ℕ → ℝ} (hg : Monotone g)
    (hx : EquidistributedMod1 x) :
    Tendsto (fun N : ℕ => total g x N / N) atTop (𝓝 (∫ t in (0:ℝ)..1, g t)) := by
  have hgap : 0 ≤ g 1 - g 0 := sub_nonneg.2 (hg zero_le_one)
  rw [tendsto_order]
  constructor
  · intro c hc
    obtain ⟨m, hm0, hmc⟩ : ∃ m : ℕ, 0 < m ∧ (g 1 - g 0) / m < (∫ t in (0:ℝ)..1, g t) - c := by
      obtain ⟨k, hk⟩ := exists_nat_gt ((g 1 - g 0) / ((∫ t in (0:ℝ)..1, g t) - c))
      refine ⟨max k 1, by positivity, ?_⟩
      have hpos : (0:ℝ) < (∫ t in (0:ℝ)..1, g t) - c := by linarith
      have hk' : ((max k 1 : ℕ) : ℝ) > (g 1 - g 0) / ((∫ t in (0:ℝ)..1, g t) - c) := by
        refine lt_of_lt_of_le hk ?_
        exact_mod_cast Nat.cast_le.mpr (le_max_left k 1)
      have hmpos : (0:ℝ) < ((max k 1 : ℕ) : ℝ) := by
        have : 0 < max k 1 := by omega
        exact_mod_cast this
      rw [div_lt_iff₀ hmpos]
      have hk'' := (div_lt_iff₀ hpos).mp hk'
      linarith [hk'']
    have hLgt : c < ∑ i ∈ Finset.range m, g ((i : ℝ) / m) * (1 / m) := by
      have h1 := upper_riemann (g := g) hg hm0
      have h2 := riemann_gap g (m := m) hm0
      linarith
    filter_upwards [(tendsto_lo (g := g) hx hm0).eventually_const_lt hLgt] with N hN
    exact lt_of_lt_of_le hN (lo_le_avg hg hm0 N)
  · intro c hc
    obtain ⟨m, hm0, hmc⟩ : ∃ m : ℕ, 0 < m ∧ (g 1 - g 0) / m < c - (∫ t in (0:ℝ)..1, g t) := by
      obtain ⟨k, hk⟩ := exists_nat_gt ((g 1 - g 0) / (c - ∫ t in (0:ℝ)..1, g t))
      refine ⟨max k 1, by positivity, ?_⟩
      have hpos : (0:ℝ) < c - ∫ t in (0:ℝ)..1, g t := by linarith
      have hk' : ((max k 1 : ℕ) : ℝ) > (g 1 - g 0) / (c - ∫ t in (0:ℝ)..1, g t) := by
        refine lt_of_lt_of_le hk ?_
        exact_mod_cast Nat.cast_le.mpr (le_max_left k 1)
      have hmpos : (0:ℝ) < ((max k 1 : ℕ) : ℝ) := by
        have : 0 < max k 1 := by omega
        exact_mod_cast this
      rw [div_lt_iff₀ hmpos]
      have hk'' := (div_lt_iff₀ hpos).mp hk'
      linarith [hk'']
    have hUlt : ∑ i ∈ Finset.range m, g (((i : ℝ) + 1) / m) * (1 / m) < c := by
      have h1 := lower_riemann (g := g) hg hm0
      have h2 := riemann_gap g (m := m) hm0
      linarith
    filter_upwards [(tendsto_hi (g := g) hx hm0).eventually_lt_const hUlt] with N hN
    exact lt_of_le_of_lt (avg_le_hi hg hm0 N) hN

/-- **BV reduction**: equidistribution averages converge to the integral for every function of
bounded variation (in Jordan form). -/
theorem bv_average_tendsto {g : ℝ → ℝ} {x : ℕ → ℝ} (hg : IsBVJordan g)
    (hx : EquidistributedMod1 x) :
    Tendsto (fun N : ℕ => total g x N / N) atTop (𝓝 (∫ t in (0:ℝ)..1, g t)) := by
  obtain ⟨g₁, g₂, hg₁, hg₂, hgeq⟩ := hg
  have hInt : (∫ t in (0:ℝ)..1, g t)
      = (∫ t in (0:ℝ)..1, g₁ t) - ∫ t in (0:ℝ)..1, g₂ t := by
    rw [← intervalIntegral.integral_sub hg₁.intervalIntegrable hg₂.intervalIntegrable]
    exact intervalIntegral.integral_congr (fun t _ => hgeq t)
  have hsplit : ∀ N : ℕ, total g x N / N = total g₁ x N / N - total g₂ x N / N := by
    intro N
    rw [← sub_div]
    congr 1
    rw [total, total, total, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => hgeq _
  simp only [hsplit, hInt]
  exact (monotone_average_tendsto hg₁ hx).sub (monotone_average_tendsto hg₂ hx)

/-- **Total over main tends to one.** For a sequence `x` equidistributed mod 1 and a test
function `g` of bounded variation with nonzero mean, the ratio of the total Weyl sum
`∑_{n<N} g (fract (x n))` to the main term `N ∫₀¹ g` tends to `1`. -/
theorem total_over_main_tendsto {g : ℝ → ℝ} {x : ℕ → ℝ} (hg : IsBVJordan g)
    (hx : EquidistributedMod1 x) (hI : (∫ t in (0:ℝ)..1, g t) ≠ 0) :
    Tendsto (fun N : ℕ => total g x N / main g N) atTop (𝓝 1) := by
  have hrw : ∀ N : ℕ, total g x N / main g N
      = (total g x N / N) / (∫ t in (0:ℝ)..1, g t) := by
    intro N
    rw [main, div_div]
  simp only [hrw]
  have := (bv_average_tendsto hg hx).div_const (∫ t in (0:ℝ)..1, g t)
  rwa [div_self hI] at this

end EquidistributionBVReduction
end Brockian

