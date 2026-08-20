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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open MeasureTheory

/-- Cauchy–Schwarz for the Lebesgue integral on `ℝ`: for continuous, compactly supported
`u, v : ℝ → ℝ` we have `∫ |u| |v| ≤ √(∫ u²) * √(∫ v²)`. -/

lemma exists_le_eq_zero_of_hasCompactSupport {f : ℝ → ℝ} (hsupp : HasCompactSupport f) (x : ℝ) :
    ∃ a : ℝ, a ≤ x ∧ f a = 0 := by
  obtain ⟨R, hR⟩ := (hsupp.isCompact.isBounded).subset_closedBall (0:ℝ)
  refine ⟨min x (-R - 1) - 1, by have := min_le_left x (-R - 1); linarith, ?_⟩
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have h1 := hR hmem
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h1
  have h2 := min_le_right x (-R - 1)
  have h3 : -(min x (-R - 1) - 1) ≤ |min x (-R - 1) - 1| := neg_le_abs _
  linarith

/-- **Gagliardo–Nirenberg interpolation inequality**, one-dimensional base case
(`p = ∞`, `q = r = 2`, interpolation parameter `θ = 1/2`).

If `f : ℝ → ℝ` is continuously differentiable with derivative `f'` and has compact support, then
`‖f‖_∞ ≤ √2 · ‖f‖_{L²}^{1/2} · ‖f'‖_{L²}^{1/2}`, stated here in the equivalent squared, pointwise
form `f x ^ 2 ≤ 2 · (∫ f²)^{1/2} · (∫ (f')²)^{1/2}`. -/
