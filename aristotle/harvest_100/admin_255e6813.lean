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
open Filter Set MeasureTheory
open scoped Topology ENNReal

namespace Brockian.EquidistributionBVReduction

/-- The (right-continuous) step function jumping from `0` to `1` at `c`. -/
noncomputable def stepFun (c : ℝ) : ℝ → ℝ := fun t => if c ≤ t then (1 : ℝ) else 0

/-- The indicator function of the window `[a, b)`, written as a difference of two step
functions. -/
noncomputable def windowFun (a b : ℝ) : ℝ → ℝ := fun t => stepFun a t - stepFun b t

/-- A sequence `x` is equidistributed mod one if, for every subinterval `[a, b) ⊆ [0, 1]`,
the proportion of the first `N` terms whose fractional part lies in `[a, b)` tends to
`b - a`, the length of the interval (i.e. its uniform/Lebesgue measure). -/
def EquidistributedMod1 (x : ℕ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
    Tendsto (fun N : ℕ =>
        (((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico a b).card : ℝ) / N)
      atTop (𝓝 (b - a))

/-- The "BV test-function" hypothesis: the Birkhoff-type averages of the sequence along every
integrable function of bounded variation on `[0, 1]` converge to the integral of that function
with respect to the uniform (Lebesgue) measure on `[0, 1]`. -/
def BVAverageConvergence (x : ℕ → ℝ) : Prop :=
  ∀ f : ℝ → ℝ, BoundedVariationOn f (Set.Icc (0 : ℝ) 1) →
    IntervalIntegrable f volume 0 1 →
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (Int.fract (x n))) / N)
      atTop (𝓝 (∫ t in (0 : ℝ)..1, f t))

/-- Variation is subadditive under differences of real-valued functions. -/
theorem eVariationOn_sub_le {s : Set ℝ} (f g : ℝ → ℝ) :
    eVariationOn (fun t => f t - g t) s ≤ eVariationOn f s + eVariationOn g s := by
  apply iSup_le
  rintro ⟨n, ⟨u, hu, us⟩⟩
  have step : ∀ i, edist (f (u (i + 1)) - g (u (i + 1))) (f (u i) - g (u i))
      ≤ edist (f (u (i + 1))) (f (u i)) + edist (g (u (i + 1))) (g (u i)) := by
    intro i
    simp only [edist_dist, Real.dist_eq]
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    calc |f (u (i + 1)) - g (u (i + 1)) - (f (u i) - g (u i))|
        = |(f (u (i + 1)) - f (u i)) + -(g (u (i + 1)) - g (u i))| := by ring_nf
      _ ≤ |f (u (i + 1)) - f (u i)| + |-(g (u (i + 1)) - g (u i))| := abs_add_le _ _
      _ = |f (u (i + 1)) - f (u i)| + |g (u (i + 1)) - g (u i)| := by rw [abs_neg]
  calc ∑ i ∈ Finset.range n, edist (f (u (i + 1)) - g (u (i + 1))) (f (u i) - g (u i))
      ≤ ∑ i ∈ Finset.range n, (edist (f (u (i + 1))) (f (u i)) + edist (g (u (i + 1))) (g (u i))) :=
        Finset.sum_le_sum fun i _ => step i
    _ = (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)))
        + ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)) := Finset.sum_add_distrib
    _ ≤ eVariationOn f s + eVariationOn g s :=
        add_le_add (eVariationOn.sum_le f n hu us) (eVariationOn.sum_le g n hu us)

theorem monotone_stepFun (c : ℝ) : Monotone (stepFun c) := by
  intro s t hst
  simp only [stepFun]
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd (h1.trans hst) h2
  · norm_num
  · exact le_rfl

theorem boundedVariationOn_stepFun (c : ℝ) :
    BoundedVariationOn (stepFun c) (Set.Icc (0 : ℝ) 1) := by
  have h := ((monotone_stepFun c).monotoneOn (Set.Icc (0 : ℝ) 1)).eVariationOn_le
    (a := 0) (b := 1) (by norm_num) (by norm_num)
  rw [Set.inter_self] at h
  exact (h.trans_lt ENNReal.ofReal_lt_top).ne

theorem boundedVariationOn_windowFun (a b : ℝ) :
    BoundedVariationOn (windowFun a b) (Set.Icc (0 : ℝ) 1) :=
  ne_top_of_le_ne_top
    (ENNReal.add_ne_top.2 ⟨boundedVariationOn_stepFun a, boundedVariationOn_stepFun b⟩)
    (eVariationOn_sub_le (stepFun a) (stepFun b))

theorem windowFun_eq_indicator {a b : ℝ} (hab : a ≤ b) (t : ℝ) :
    windowFun a b t = if t ∈ Set.Ico a b then (1 : ℝ) else 0 := by
  simp only [windowFun, stepFun, Set.mem_Ico]
  split_ifs with h1 h2 h3 <;> simp_all <;> linarith

theorem intervalIntegrable_stepFun (c : ℝ) : IntervalIntegrable (stepFun c) volume 0 1 :=
  ((monotone_stepFun c).monotoneOn _).intervalIntegrable

theorem intervalIntegrable_windowFun (a b : ℝ) :
    IntervalIntegrable (windowFun a b) volume 0 1 :=
  (intervalIntegrable_stepFun a).sub (intervalIntegrable_stepFun b)

theorem integral_stepFun {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    (∫ t in (0 : ℝ)..1, stepFun c t) = 1 - c := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  have hset : (fun t => stepFun c t) = Set.indicator (Set.Ici c) (fun _ => (1 : ℝ)) := by
    funext t; simp [stepFun, Set.indicator_apply]
  rw [hset, MeasureTheory.setIntegral_indicator measurableSet_Ici,
    MeasureTheory.setIntegral_const]
  have hvol : volume (Set.Ioc (0 : ℝ) 1 ∩ Set.Ici c) = ENNReal.ofReal (1 - c) := by
    apply le_antisymm
    · calc volume (Set.Ioc (0 : ℝ) 1 ∩ Set.Ici c) ≤ volume (Set.Icc c 1) := by
            apply measure_mono
            rintro t ⟨⟨_, h2⟩, h3⟩
            exact ⟨h3, h2⟩
        _ = ENNReal.ofReal (1 - c) := by rw [Real.volume_Icc]
    · calc ENNReal.ofReal (1 - c) = volume (Set.Ioo c 1) := by rw [Real.volume_Ioo]
        _ ≤ volume (Set.Ioc (0 : ℝ) 1 ∩ Set.Ici c) := by
            apply measure_mono
            rintro t ⟨h1, h2⟩
            exact ⟨⟨lt_of_le_of_lt hc h1, h2.le⟩, h1.le⟩
  rw [measureReal_def, hvol, ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ 1 - c), smul_eq_mul,
    mul_one]

theorem integral_windowFun {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (∫ t in (0 : ℝ)..1, windowFun a b t) = b - a := by
  have : (∫ t in (0 : ℝ)..1, windowFun a b t)
      = (∫ t in (0 : ℝ)..1, stepFun a t) - ∫ t in (0 : ℝ)..1, stepFun b t :=
    intervalIntegral.integral_sub (intervalIntegrable_stepFun a) (intervalIntegrable_stepFun b)
  rw [this, integral_stepFun ha (hab.trans hb), integral_stepFun (ha.trans hab) hb]
  ring

theorem sum_windowFun {a b : ℝ} (hab : a ≤ b) (x : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, windowFun a b (Int.fract (x n))) =
      (((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico a b).card : ℝ) := by
  simp only [windowFun_eq_indicator hab]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
  simp

/-- **Equidistribution from convergence of bounded-variation averages.**

If the averages `(1/N) ∑_{n < N} f (frac (x n))` converge to `∫₀¹ f` for every integrable
function `f` of bounded variation on `[0, 1]`, then the sequence `x` is equidistributed mod one
with respect to the uniform measure.  The proof applies the hypothesis to the indicator function
of a window `[a, b)`, whose bounded variation and integrability are established here rather than
assumed, so the statement carries no auxiliary named hypothesis. -/
theorem equidistribution_of_BV_uniform (x : ℕ → ℝ) (h : BVAverageConvergence x) :
    EquidistributedMod1 x := by
  intro a b ha hab hb
  have key := h (windowFun a b) (boundedVariationOn_windowFun a b)
    (intervalIntegrable_windowFun a b)
  rw [integral_windowFun ha hab hb] at key
  simpa only [sum_windowFun hab x] using key

end Brockian.EquidistributionBVReduction

