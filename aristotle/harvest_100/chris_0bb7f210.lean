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

open scoped BigOperators
open Filter Set MeasureTheory Topology

namespace Brockian.EquidistributionBVReduction

/-- The indicator function of the half-open interval `[a, b)`, as a real-valued function. -/
noncomputable def indicatorIco (a b : ℝ) : ℝ → ℝ :=
  Set.indicator (Set.Ico a b) (fun _ => (1 : ℝ))

lemma indicatorIco_apply (a b : ℝ) (t : ℝ) :
    indicatorIco a b t = if t ∈ Set.Ico a b then 1 else 0 := by
  simp [indicatorIco, Set.indicator_apply]

/-- Subadditivity of the total variation with respect to differences of real-valued functions. -/
lemma eVariationOn_sub_le {s : Set ℝ} (g h : ℝ → ℝ) :
    eVariationOn (fun t => g t - h t) s ≤ eVariationOn g s + eVariationOn h s := by
  refine iSup_le ?_
  rintro ⟨n, u, hu, us⟩
  have key : ∀ i : ℕ, edist (g (u (i + 1)) - h (u (i + 1))) (g (u i) - h (u i))
      ≤ edist (g (u (i + 1))) (g (u i)) + edist (h (u (i + 1))) (h (u i)) := by
    intro i
    calc edist (g (u (i + 1)) - h (u (i + 1))) (g (u i) - h (u i))
        ≤ edist (g (u (i + 1)) - h (u (i + 1))) (g (u i) - h (u (i + 1)))
          + edist (g (u i) - h (u (i + 1))) (g (u i) - h (u i)) := edist_triangle _ _ _
      _ = edist (g (u (i + 1))) (g (u i)) + edist (h (u (i + 1))) (h (u i)) := by
          rw [edist_sub_right, edist_sub_left]
  calc (∑ i ∈ Finset.range n, edist (g (u (i + 1)) - h (u (i + 1))) (g (u i) - h (u i)))
      ≤ ∑ i ∈ Finset.range n,
          (edist (g (u (i + 1))) (g (u i)) + edist (h (u (i + 1))) (h (u i))) :=
        Finset.sum_le_sum fun i _ => key i
    _ = (∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)))
          + ∑ i ∈ Finset.range n, edist (h (u (i + 1))) (h (u i)) := Finset.sum_add_distrib
    _ ≤ eVariationOn g s + eVariationOn h s :=
        add_le_add (eVariationOn.sum_le g n hu us) (eVariationOn.sum_le h n hu us)

/-- The indicator of a half-line `[a, ∞)` is monotone. -/
lemma indicatorIci_monotone (a : ℝ) :
    Monotone (Set.indicator (Set.Ici a) (fun _ => (1 : ℝ))) := by
  intro s t hst
  simp only [Set.indicator_apply, Set.mem_Ici]
  split_ifs with h1 h2 h2 <;> norm_num
  linarith

/-- A monotone function has bounded variation on `[0, 1]`. -/
lemma boundedVariationOn_of_monotone {f : ℝ → ℝ} (hf : Monotone f) :
    BoundedVariationOn f (Set.Icc (0 : ℝ) 1) := by
  have h := (hf.monotoneOn (Set.Icc (0:ℝ) 1)).eVariationOn_le (a := 0) (b := 1)
    (by norm_num) (by norm_num)
  rw [Set.inter_self] at h
  exact ne_top_of_le_ne_top (by simp) h

/-- For `a ≤ b`, the indicator of `[a, b)` is the difference of the indicators of the
half-lines `[a, ∞)` and `[b, ∞)`. -/
lemma indicatorIco_eq_sub {a b : ℝ} (hab : a ≤ b) :
    indicatorIco a b = fun t => Set.indicator (Set.Ici a) (fun _ => (1:ℝ)) t
      - Set.indicator (Set.Ici b) (fun _ => (1:ℝ)) t := by
  funext t
  simp only [indicatorIco, Set.indicator_apply, Set.mem_Ico, Set.mem_Ici]
  by_cases h1 : a ≤ t
  · by_cases h2 : b ≤ t
    · rw [if_neg (fun hc => absurd hc.2 (not_lt.2 h2)), if_pos h1, if_pos h2]; ring
    · rw [if_pos ⟨h1, not_le.1 h2⟩, if_pos h1, if_neg h2]; ring
  · rw [if_neg (fun hc => h1 hc.1), if_neg h1, if_neg (fun hc => h1 (hab.trans hc))]; ring

/-- The indicator of `[a, b)` (with `a ≤ b`) has bounded variation on `[0, 1]`. -/
lemma indicatorIco_boundedVariationOn {a b : ℝ} (hab : a ≤ b) :
    BoundedVariationOn (indicatorIco a b) (Set.Icc (0 : ℝ) 1) := by
  rw [BoundedVariationOn, indicatorIco_eq_sub hab]
  refine ne_top_of_le_ne_top ?_ (eVariationOn_sub_le _ _)
  exact ENNReal.add_ne_top.2
    ⟨boundedVariationOn_of_monotone (indicatorIci_monotone a),
      boundedVariationOn_of_monotone (indicatorIci_monotone b)⟩

lemma indicatorIco_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable (indicatorIco a b) volume 0 1 := by
  have h : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume 0 1 := intervalIntegrable_const
  exact ⟨h.1.indicator measurableSet_Ico, h.2.indicator measurableSet_Ico⟩

lemma integral_indicatorIco {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (∫ t in (0:ℝ)..1, indicatorIco a b t) = b - a := by
  have hvol : volume (Set.Ico a b ∩ Set.Ioc (0:ℝ) 1) = ENNReal.ofReal (b - a) := by
    refine le_antisymm ?_ ?_
    · calc volume (Set.Ico a b ∩ Set.Ioc (0:ℝ) 1) ≤ volume (Set.Icc a b) :=
            measure_mono fun t ht => ⟨ht.1.1, ht.1.2.le⟩
        _ = ENNReal.ofReal (b - a) := by rw [Real.volume_Icc]
    · calc ENNReal.ofReal (b - a) = volume (Set.Ioo a b) := by rw [Real.volume_Ioo]
        _ ≤ volume (Set.Ico a b ∩ Set.Ioc (0:ℝ) 1) :=
            measure_mono fun t ht => ⟨⟨ht.1.le, ht.2⟩, lt_of_le_of_lt ha ht.1, ht.2.le.trans hb⟩
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  unfold indicatorIco
  rw [MeasureTheory.integral_indicator measurableSet_Ico,
    MeasureTheory.Measure.restrict_restrict measurableSet_Ico,
    MeasureTheory.integral_const]
  simp [MeasureTheory.measureReal_def, hvol,
    ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ b - a)]

lemma sum_indicatorIco_eq_card (x : ℕ → ℝ) (a b : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, indicatorIco a b (x n))
      = (((Finset.range N).filter (fun n => x n ∈ Set.Ico a b)).card : ℝ) := by
  classical
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun n _ => ?_
  simp [indicatorIco, Set.indicator_apply]

/-- **Reduction of equidistribution to bounded-variation test functions.**

If the Cesàro averages of `f (x n)` converge to `∫₀¹ f` for every function `f` of bounded
variation on `[0, 1]` which is interval integrable there (the "BV-uniform" hypothesis), then the
sequence `x` is equidistributed: for every subinterval `[a, b) ⊆ [0, 1]`, the proportion of
indices `n < N` with `x n ∈ [a, b)` tends to `b - a`.

The proof applies the hypothesis to the indicator function of `[a, b)`, which is shown here to
be of bounded variation on `[0, 1]` (it is the difference of two monotone half-line indicators)
and interval integrable, with `∫₀¹ 1_{[a,b)} = b - a`. -/
theorem equidistribution_of_BV_uniform (x : ℕ → ℝ)
    (hBV : ∀ f : ℝ → ℝ, BoundedVariationOn f (Set.Icc (0:ℝ) 1) →
      IntervalIntegrable f volume 0 1 →
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (x n)) / N) atTop
        (𝓝 (∫ t in (0:ℝ)..1, f t)))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto
      (fun N : ℕ => (((Finset.range N).filter (fun n => x n ∈ Set.Ico a b)).card : ℝ) / N)
      atTop (𝓝 (b - a)) := by
  have h := hBV (indicatorIco a b) (indicatorIco_boundedVariationOn hab)
    (indicatorIco_intervalIntegrable a b)
  rw [integral_indicatorIco ha hab hb] at h
  simpa [sum_indicatorIco_eq_card] using h

end Brockian.EquidistributionBVReduction

