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
# Reduction of equidistribution to bounded–variation test functions

Let `x : ℕ → ℝ` be a sequence.  We say that the *bounded variation averages of `x`
converge* if for every real function `f` of bounded variation on `[0,1]` the Birkhoff-type
averages of `f` along the fractional parts of `x` converge to `∫_0^1 f`.

The main result, `Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform`,
says that this hypothesis on `x` forces `x` to be uniformly distributed mod `1`:
the proportion of the first `N` fractional parts falling into a subinterval `[a,b) ⊆ [0,1]`
tends to its length `b - a`.

The point of the reduction is that indicator functions of intervals are of bounded
variation; this is proved here from scratch (`Brockian.EquidistributionBVReduction.boundedVariationOn_indicator_Ico`),
via a subadditivity estimate for `eVariationOn` and the fact that the two half-line
indicators `1_{[a,∞)}` and `1_{[b,∞)}` are monotone.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace Brockian
namespace EquidistributionBVReduction

/-- A sequence `x : ℕ → ℝ` is *uniformly distributed mod 1* if for every subinterval
`[a,b) ⊆ [0,1]`, the proportion of `n < N` with `Int.fract (x n) ∈ [a, b)` tends to `b - a`. -/
def UniformlyDistributedMod1 (x : ℕ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
    Tendsto
      (fun N : ℕ =>
        (((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico a b).card : ℝ) / (N : ℝ))
      atTop (𝓝 (b - a))

/-- The averages of every function of bounded variation on `[0,1]`, evaluated along the
fractional parts of `x`, converge to the integral of the function over `[0,1]`. -/
def BVAveragesConverge (x : ℕ → ℝ) : Prop :=
  ∀ f : ℝ → ℝ, BoundedVariationOn f (Set.Icc (0 : ℝ) 1) →
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (Int.fract (x n))) / (N : ℝ))
      atTop (𝓝 (∫ t in (0 : ℝ)..1, f t))

/-! ### Bounded variation of interval indicators -/

/-- Subadditivity of the extended variation with respect to differences of functions. -/
theorem eVariationOn_sub_le {α : Type*} [LinearOrder α] (f g : α → ℝ) (s : Set α) :
    eVariationOn (fun t => f t - g t) s ≤ eVariationOn f s + eVariationOn g s := by
  refine iSup_le ?_
  rintro ⟨n, ⟨u, hu, us⟩⟩
  have key : ∀ i : ℕ,
      edist (f (u (i + 1)) - g (u (i + 1))) (f (u i) - g (u i)) ≤
        edist (f (u (i + 1))) (f (u i)) + edist (g (u (i + 1))) (g (u i)) := by
    intro i
    simp only [edist_dist, Real.dist_eq]
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc |f (u (i + 1)) - g (u (i + 1)) - (f (u i) - g (u i))|
        = |(f (u (i + 1)) - f (u i)) - (g (u (i + 1)) - g (u i))| := by ring_nf
      _ ≤ |f (u (i + 1)) - f (u i)| + |g (u (i + 1)) - g (u i)| := abs_sub _ _
  calc ∑ i ∈ Finset.range n, edist (f (u (i + 1)) - g (u (i + 1))) (f (u i) - g (u i))
      ≤ ∑ i ∈ Finset.range n,
          (edist (f (u (i + 1))) (f (u i)) + edist (g (u (i + 1))) (g (u i))) :=
        Finset.sum_le_sum fun i _ => key i
    _ = (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)))
          + ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)) := Finset.sum_add_distrib
    _ ≤ eVariationOn f s + eVariationOn g s :=
        add_le_add (eVariationOn.sum_le f n hu us) (eVariationOn.sum_le g n hu us)

/-- The indicator of a half line `[c, ∞)` has bounded variation on `[0,1]`. -/
theorem boundedVariationOn_indicator_Ici (c : ℝ) :
    BoundedVariationOn (fun t : ℝ => if c ≤ t then (1 : ℝ) else 0) (Set.Icc (0 : ℝ) 1) := by
  have hmono : Monotone fun t : ℝ => if c ≤ t then (1 : ℝ) else 0 := by
    intro s t hst
    by_cases hs : c ≤ s
    · simp [hs, hs.trans hst]
    · simp only [hs, if_false]
      split <;> norm_num
  have h := (hmono.monotoneOn (Set.Icc (0 : ℝ) 1)).eVariationOn_le
    (a := (0 : ℝ)) (b := (1 : ℝ)) (by norm_num) (by norm_num)
  rw [Set.inter_self] at h
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h

/-- The indicator function of an interval `[a, b)` has bounded variation on `[0,1]`. -/
theorem boundedVariationOn_indicator_Ico {a b : ℝ} (hab : a ≤ b) :
    BoundedVariationOn (Set.indicator (Set.Ico a b) (fun _ => (1 : ℝ))) (Set.Icc (0 : ℝ) 1) := by
  have heq : Set.EqOn (Set.indicator (Set.Ico a b) (fun _ => (1 : ℝ)))
      (fun t : ℝ => (if a ≤ t then (1 : ℝ) else 0) - (if b ≤ t then (1 : ℝ) else 0))
      (Set.Icc (0 : ℝ) 1) := by
    intro t _
    by_cases hb : b ≤ t
    · have ha : a ≤ t := hab.trans hb
      simp [ha, hb]
    · push_neg at hb
      by_cases ha : a ≤ t
      · have : t ∈ Set.Ico a b := ⟨ha, hb⟩
        simp [Set.indicator_of_mem this, ha, not_le.2 hb]
      · push_neg at ha
        simp [not_le.2 ha, not_le.2 hb]
  unfold BoundedVariationOn
  rw [eVariationOn.eq_of_eqOn heq]
  refine ne_top_of_le_ne_top ?_ (eVariationOn_sub_le _ _ _)
  exact ENNReal.add_ne_top.2 ⟨boundedVariationOn_indicator_Ici a, boundedVariationOn_indicator_Ici b⟩

/-! ### The integral of an interval indicator -/

/-- The integral over `[0,1]` of the indicator of `[a,b) ⊆ [0,1]` is `b - a`. -/
theorem integral_indicator_Ico {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (∫ t in (0 : ℝ)..1, Set.indicator (Set.Ico a b) (fun _ => (1 : ℝ)) t) = b - a := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [MeasureTheory.integral_indicator measurableSet_Ico]
  have hvol : (volume.restrict (Set.Ioc (0 : ℝ) 1)) (Set.Ico a b) = ENNReal.ofReal (b - a) := by
    rw [Measure.restrict_apply measurableSet_Ico]
    have h1 : Set.Ioo a b ⊆ Set.Ico a b ∩ Set.Ioc (0 : ℝ) 1 := by
      rintro t ⟨h1, h2⟩
      exact ⟨⟨h1.le, h2⟩, lt_of_le_of_lt ha h1, (h2.le.trans hb)⟩
    have h2 : Set.Ico a b ∩ Set.Ioc (0 : ℝ) 1 ⊆ Set.Icc a b := fun t ht => ⟨ht.1.1, ht.1.2.le⟩
    have hle1 := measure_mono (μ := (volume : Measure ℝ)) h1
    have hle2 := measure_mono (μ := (volume : Measure ℝ)) h2
    rw [Real.volume_Ioo] at hle1
    rw [Real.volume_Icc] at hle2
    exact le_antisymm hle2 hle1
  simp only [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
  rw [MeasureTheory.measureReal_def, hvol, ENNReal.toReal_ofReal (by linarith)]

/-! ### The main reduction -/

/-- **Reduction of equidistribution to bounded variation test functions.**
If the averages along `x` of every function of bounded variation on `[0,1]` converge to the
corresponding integral, then `x` is uniformly distributed mod `1`. -/
theorem equidistribution_of_BV_uniform (x : ℕ → ℝ) (h : BVAveragesConverge x) :
    UniformlyDistributedMod1 x := by
  intro a b ha hab hb
  have key := h (Set.indicator (Set.Ico a b) fun _ => (1 : ℝ))
    (boundedVariationOn_indicator_Ico hab)
  rw [integral_indicator_Ico ha hab hb] at key
  have hsum : ∀ N : ℕ,
      (∑ n ∈ Finset.range N, Set.indicator (Set.Ico a b) (fun _ => (1 : ℝ)) (Int.fract (x n)))
        = (((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico a b).card : ℝ) := by
    intro N
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hn : Int.fract (x n) ∈ Set.Ico a b <;> simp [hn]
  simpa only [hsum] using key

end EquidistributionBVReduction
end Brockian

