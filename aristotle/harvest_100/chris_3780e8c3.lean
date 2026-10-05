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

open scoped BigOperators ENNReal
open Set Filter MeasureTheory

namespace Brockian
namespace EquidistributionBVReduction

/-! ## Variation of a difference -/

/-- The variation of a difference of two real-valued functions is at most the sum of the
variations. -/
theorem eVariationOn_sub_le {α : Type*} [LinearOrder α] (f g : α → ℝ) (s : Set α) :
    eVariationOn (fun x => f x - g x) s ≤ eVariationOn f s + eVariationOn g s := by
  apply iSup_le
  rintro ⟨n, u, hu, us⟩
  dsimp only
  calc ∑ i ∈ Finset.range n, edist (f (u (i + 1)) - g (u (i + 1))) (f (u i) - g (u i))
      ≤ ∑ i ∈ Finset.range n,
          (edist (f (u (i + 1))) (f (u i)) + edist (g (u (i + 1))) (g (u i))) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [edist_dist, edist_dist, edist_dist,
          ← ENNReal.ofReal_add dist_nonneg dist_nonneg]
        apply ENNReal.ofReal_le_ofReal
        simp only [Real.dist_eq]
        have h : f (u (i + 1)) - g (u (i + 1)) - (f (u i) - g (u i))
            = (f (u (i + 1)) - f (u i)) + (-(g (u (i + 1)) - g (u i))) := by ring
        rw [h]
        exact (abs_add_le _ _).trans (by rw [abs_neg])
    _ = (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)))
          + ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)) := Finset.sum_add_distrib
    _ ≤ eVariationOn f s + eVariationOn g s :=
        add_le_add (eVariationOn.sum_le f n hu us) (eVariationOn.sum_le g n hu us)

/-- The indicator function of a right-infinite ray is monotone. -/
theorem monotone_indicator_Ici (a : ℝ) :
    Monotone (Set.indicator (Set.Ici a) (fun _ => (1 : ℝ))) := by
  intro x y h
  by_cases hx : a ≤ x <;> by_cases hy : a ≤ y <;> simp [hx, hy]
  all_goals linarith

/-- The indicator of a ray has bounded variation on `[0, 1]`. -/
theorem boundedVariationOn_indicator_Ici (a : ℝ) :
    BoundedVariationOn (Set.indicator (Set.Ici a) (fun _ => (1 : ℝ))) (Set.Icc (0 : ℝ) 1) := by
  have h := ((monotone_indicator_Ici a).monotoneOn (Set.Icc (0 : ℝ) 1)).eVariationOn_le
    (a := 0) (b := 1) (by norm_num) (by norm_num)
  rw [Set.inter_self] at h
  exact ne_top_of_le_ne_top (by simp) h

/-- On the whole line, the indicator of `[a, b)` is the difference of the indicators of the
rays `[a, ∞)` and `[b, ∞)`. -/
theorem indicator_Ico_eq_sub {a b : ℝ} (hab : a ≤ b) (t : ℝ) :
    Set.indicator (Set.Ico a b) (fun _ => (1 : ℝ)) t =
      Set.indicator (Set.Ici a) (fun _ => (1 : ℝ)) t -
        Set.indicator (Set.Ici b) (fun _ => (1 : ℝ)) t := by
  by_cases ha : a ≤ t <;> by_cases hb : b ≤ t <;>
    simp [Set.indicator_apply, ha, hb]
  all_goals linarith

/-- The indicator of an interval `[a, b)` has bounded variation on `[0, 1]`. -/
theorem boundedVariationOn_indicator_Ico {a b : ℝ} (hab : a ≤ b) :
    BoundedVariationOn (Set.indicator (Set.Ico a b) (fun _ => (1 : ℝ))) (Set.Icc (0 : ℝ) 1) := by
  have heq : eVariationOn (Set.indicator (Set.Ico a b) (fun _ => (1 : ℝ))) (Set.Icc (0 : ℝ) 1)
      = eVariationOn (fun t => Set.indicator (Set.Ici a) (fun _ => (1 : ℝ)) t
          - Set.indicator (Set.Ici b) (fun _ => (1 : ℝ)) t) (Set.Icc (0 : ℝ) 1) :=
    eVariationOn.eq_of_eqOn fun t _ => indicator_Ico_eq_sub hab t
  show eVariationOn (Set.indicator (Set.Ico a b) (fun _ => (1 : ℝ))) (Set.Icc (0 : ℝ) 1) ≠ ⊤
  rw [heq]
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2
    ⟨boundedVariationOn_indicator_Ici a, boundedVariationOn_indicator_Ici b⟩)
    (eVariationOn_sub_le _ _ _)

/-- The integral of the indicator of `[a, b) ⊆ [0, 1]` over `[0, 1]` is `b - a`. -/
theorem integral_indicator_Ico {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (∫ t in (0 : ℝ)..1, Set.indicator (Set.Ico a b) (fun _ => (1 : ℝ)) t) = b - a := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    MeasureTheory.setIntegral_indicator measurableSet_Ico]
  have hsub1 : Set.Ioo a b ⊆ Set.Ioc (0 : ℝ) 1 ∩ Set.Ico a b := fun t ht =>
    ⟨⟨lt_of_le_of_lt ha ht.1, le_of_lt (lt_of_lt_of_le ht.2 hb)⟩, ⟨le_of_lt ht.1, ht.2⟩⟩
  have hsub2 : Set.Ioc (0 : ℝ) 1 ∩ Set.Ico a b ⊆ Set.Ico a b := Set.inter_subset_right
  have hm : volume (Set.Ioc (0 : ℝ) 1 ∩ Set.Ico a b) = ENNReal.ofReal (b - a) := by
    refine le_antisymm ?_ ?_
    · simpa using measure_mono (μ := (volume : Measure ℝ)) hsub2
    · simpa using measure_mono (μ := (volume : Measure ℝ)) hsub1
  rw [MeasureTheory.setIntegral_const, measureReal_def, hm,
    ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ b - a), smul_eq_mul, mul_one]

/-! ## Configuration counts -/

open scoped Classical in
/-- `configCount x s N` is the number of indices `n < N` for which the fractional part of
`x n` lies in the "configuration set" `s`. -/
noncomputable def configCount (x : ℕ → ℝ) (s : Set ℝ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => Int.fract (x n) ∈ s)).card

/-- A sequence is *BV-equidistributed* mod 1 if the Birkhoff averages of every function of
bounded variation on `[0, 1]` converge to its integral over `[0, 1]`. -/
def BVEquidistributed (x : ℕ → ℝ) : Prop :=
  ∀ f : ℝ → ℝ, BoundedVariationOn f (Set.Icc (0 : ℝ) 1) →
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (Int.fract (x n))) / N) atTop
      (nhds (∫ t in (0 : ℝ)..1, f t))

/-- Rewriting a configuration count as a Birkhoff sum of an indicator. -/
theorem sum_indicator_eq_configCount (x : ℕ → ℝ) (s : Set ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, Set.indicator s (fun _ => (1 : ℝ)) (Int.fract (x n))) =
      (configCount x s N : ℝ) := by
  classical
  rw [configCount]
  simp [Set.indicator_apply, Finset.sum_boole]

/-- **Configuration-count density from bounded variation.**

If a sequence is BV-equidistributed mod 1, then for every subinterval `[a, b) ⊆ [0, 1]` the
density of the indices `n < N` whose fractional part falls in `[a, b)` converges to the
length `b - a`.

The statement is unconditional in the sense that no auxiliary "known result" is assumed as a
hypothesis: the facts that indicators of intervals are of bounded variation and that they
integrate to the length of the interval are proved here. -/
theorem configCount_density_of_BV (x : ℕ → ℝ) (hx : BVEquidistributed x)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (fun N : ℕ => (configCount x (Set.Ico a b) N : ℝ) / N) atTop (nhds (b - a)) := by
  have h := hx _ (boundedVariationOn_indicator_Ico hab)
  rw [integral_indicator_Ico ha hab hb] at h
  simpa only [sum_indicator_eq_configCount] using h

end EquidistributionBVReduction
end Brockian

