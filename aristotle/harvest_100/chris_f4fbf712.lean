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
# Equidistribution from uniform averaging against functions of bounded variation

If a real sequence `x : ℕ → ℝ` has the property that for *every* function `f : ℝ → ℝ` of
bounded variation on `[0,1]` the Cesàro averages `(1/N) ∑_{n < N} f (x n)` converge to
`∫_0^1 f`, then `x` is equidistributed in `[0,1]`: for every subinterval `[a,b) ⊆ [0,1]`
the proportion of indices `n < N` with `x n ∈ [a,b)` converges to `b - a`.

The proof tests the hypothesis on the indicator function of `[a, b)`.  The two facts that
this reduction relies on are proved here rather than assumed, making the statement
unconditional:

* `Brockian.EquidistributionBVReduction.boundedVariationOn_indicator_Ico` : the indicator
  function of an interval `[a, b)` has bounded variation on `[0,1]`;
* `Brockian.EquidistributionBVReduction.intervalIntegral_indicator_Ico` : its integral over
  `[0,1]` equals `b - a` whenever `0 ≤ a ≤ b ≤ 1`.
-/

namespace Brockian
namespace EquidistributionBVReduction

open Filter Set MeasureTheory
open scoped Topology ENNReal

/-- The Heaviside-type step function `t ↦ 1` if `a ≤ t`, and `0` otherwise. -/
noncomputable def stepGe (a : ℝ) : ℝ → ℝ := fun t => if a ≤ t then 1 else 0

lemma monotone_stepGe (a : ℝ) : Monotone (stepGe a) := by
  intro s t hst
  simp only [stepGe]
  split_ifs with h₁ h₂ h₂
  · exact le_rfl
  · exact absurd (h₁.trans hst) h₂
  · norm_num
  · exact le_rfl

/-- Any monotone function has bounded variation on `[0,1]`. -/
lemma boundedVariationOn_of_monotone {f : ℝ → ℝ} (hf : Monotone f) :
    BoundedVariationOn f (Icc (0:ℝ) 1) := by
  have h := (hf.monotoneOn (Icc (0:ℝ) 1)).eVariationOn_le (a := (0:ℝ)) (b := 1)
    (by norm_num) (by norm_num)
  rw [Set.inter_self] at h
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h

/-- The variation of a difference of two functions is bounded by the sum of their
variations. -/
lemma eVariationOn_sub_le (f g : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (fun t => f t - g t) s ≤ eVariationOn f s + eVariationOn g s := by
  apply iSup_le
  rintro ⟨n, ⟨u, hu, us⟩⟩
  calc ∑ i ∈ Finset.range n, edist (f (u (i + 1)) - g (u (i + 1))) (f (u i) - g (u i))
      ≤ ∑ i ∈ Finset.range n,
          (edist (f (u (i + 1))) (f (u i)) + edist (g (u (i + 1))) (g (u i))) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [edist_dist, edist_dist, edist_dist, ← ENNReal.ofReal_add dist_nonneg dist_nonneg]
        refine ENNReal.ofReal_le_ofReal ?_
        simp only [Real.dist_eq]
        have hrw : f (u (i + 1)) - g (u (i + 1)) - (f (u i) - g (u i))
            = (f (u (i + 1)) - f (u i)) - (g (u (i + 1)) - g (u i)) := by ring
        rw [hrw]
        exact abs_sub _ _
    _ = (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)))
          + ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)) := Finset.sum_add_distrib
    _ ≤ _ := add_le_add (eVariationOn.sum_le f n hu us) (eVariationOn.sum_le g n hu us)

lemma boundedVariationOn_sub {f g : ℝ → ℝ} {s : Set ℝ} (hf : BoundedVariationOn f s)
    (hg : BoundedVariationOn g s) : BoundedVariationOn (fun t => f t - g t) s := by
  refine ne_top_of_le_ne_top ?_ (eVariationOn_sub_le f g s)
  exact ENNReal.add_ne_top.2 ⟨hf, hg⟩

lemma indicator_Ico_eq_sub {a b : ℝ} (hab : a ≤ b) (t : ℝ) :
    Set.indicator (Ico a b) (fun _ => (1:ℝ)) t = stepGe a t - stepGe b t := by
  simp only [Set.indicator_apply, stepGe, Set.mem_Ico]
  split_ifs with h1 h2 h3 h3 h4 <;> simp_all <;> linarith

/-- **Discharged hypothesis (1).** The indicator function of an interval `[a, b)` has bounded
variation on `[0,1]`. -/
lemma boundedVariationOn_indicator_Ico {a b : ℝ} (hab : a ≤ b) :
    BoundedVariationOn (Set.indicator (Ico a b) (fun _ => (1:ℝ))) (Icc (0:ℝ) 1) := by
  have hBV : BoundedVariationOn (fun t => stepGe a t - stepGe b t) (Icc (0:ℝ) 1) :=
    boundedVariationOn_sub (boundedVariationOn_of_monotone (monotone_stepGe a))
      (boundedVariationOn_of_monotone (monotone_stepGe b))
  have : (Set.indicator (Ico a b) (fun _ => (1:ℝ))) = fun t => stepGe a t - stepGe b t :=
    funext (indicator_Ico_eq_sub hab)
  rw [this]
  exact hBV

/-- **Discharged hypothesis (2).** The integral of the indicator of `[a,b) ⊆ [0,1]` over `[0,1]`
is `b - a`. -/
lemma intervalIntegral_indicator_Ico {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (∫ t in (0:ℝ)..1, Set.indicator (Ico a b) (fun _ => (1:ℝ)) t) = b - a := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    MeasureTheory.setIntegral_indicator measurableSet_Ico]
  have hsub : Ioo a b ⊆ Ioc (0:ℝ) 1 ∩ Ico a b := fun t ht =>
    ⟨⟨lt_of_le_of_lt ha ht.1, le_trans ht.2.le hb⟩, ⟨ht.1.le, ht.2⟩⟩
  have hvol : volume (Ioc (0:ℝ) 1 ∩ Ico a b) = ENNReal.ofReal (b - a) := by
    refine le_antisymm ?_ ?_
    · calc volume (Ioc (0:ℝ) 1 ∩ Ico a b) ≤ volume (Ico a b) := measure_mono Set.inter_subset_right
        _ = ENNReal.ofReal (b - a) := by simp
    · calc ENNReal.ofReal (b - a) = volume (Ioo a b) := by simp
        _ ≤ _ := measure_mono hsub
  rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, hvol,
    ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ b - a), smul_eq_mul, mul_one]

lemma sum_indicator_eq_card (x : ℕ → ℝ) (a b : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, Set.indicator (Ico a b) (fun _ => (1:ℝ)) (x n) =
      (((Finset.range N).filter fun n => x n ∈ Ico a b).card : ℝ) := by
  simp [Set.indicator_apply, Finset.sum_boole]

/-- **Equidistribution from uniform averaging against BV functions.**

If the Cesàro averages of `f ∘ x` converge to `∫_0^1 f` for every function `f` of bounded
variation on `[0,1]`, then the sequence `x` is equidistributed: for `0 ≤ a ≤ b ≤ 1` the
proportion of indices `n < N` with `x n ∈ [a, b)` tends to `b - a`. -/
theorem equidistribution_of_BV_uniform (x : ℕ → ℝ)
    (h : ∀ f : ℝ → ℝ, BoundedVariationOn f (Icc (0:ℝ) 1) →
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (x n)) / N) atTop
        (𝓝 (∫ t in (0:ℝ)..1, f t)))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (fun N : ℕ => (((Finset.range N).filter fun n => x n ∈ Ico a b).card : ℝ) / N)
      atTop (𝓝 (b - a)) := by
  have key := h _ (boundedVariationOn_indicator_Ico hab)
  rw [intervalIntegral_indicator_Ico ha hab hb] at key
  simpa only [sum_indicator_eq_card x a b] using key

end EquidistributionBVReduction
end Brockian

