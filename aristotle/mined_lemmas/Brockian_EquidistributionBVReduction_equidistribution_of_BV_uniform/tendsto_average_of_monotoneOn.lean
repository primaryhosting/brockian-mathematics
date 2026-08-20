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

open Filter Finset MeasureTheory
open scoped Topology BigOperators Classical

namespace Brockian
namespace EquidistributionBVReduction

/-- The number of indices `n < N` for which the fractional part of `x n` lies in `[a, b)`. -/

theorem tendsto_average_of_monotoneOn {x : ℕ → ℝ} (hx : UniformlyDistributedMod1 x)
    {g : ℝ → ℝ} (hg : MonotoneOn g (Set.Icc (0:ℝ) 1)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, g (Int.fract (x n))) / N) atTop
      (𝓝 (∫ t in (0:ℝ)..1, g t)) := by
  set G : ℝ → ℝ := fun y => g (min 1 (max 0 y)) with hGdef
  have hmem : ∀ y : ℝ, min 1 (max 0 y) ∈ Set.Icc (0:ℝ) 1 :=
    fun y => ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩
  have hGmono : Monotone G := fun a b hab =>
    hg (hmem a) (hmem b) (min_le_min le_rfl (max_le_max le_rfl hab))
  have hGeq : Set.EqOn g G (Set.Icc (0:ℝ) 1) := by
    intro y hy
    simp [hGdef, max_eq_right hy.1, min_eq_right hy.2]
  have h1 : ∀ n : ℕ, g (Int.fract (x n)) = G (Int.fract (x n)) := fun n =>
    hGeq ⟨Int.fract_nonneg _, le_of_lt (Int.fract_lt_one _)⟩
  have h2 : (∫ t in (0:ℝ)..1, g t) = ∫ t in (0:ℝ)..1, G t :=
    intervalIntegral.integral_congr (by rwa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)])
  simp only [h1, h2]
  exact tendsto_average_of_monotone hx hGmono

/-- **Equidistribution against functions of bounded variation.**
If a sequence `x : ℕ → ℝ` is uniformly distributed mod 1, then for every function `f` of bounded
variation on `[0,1]` the averages `(1/N) ∑_{n < N} f (fract (x n))` converge to `∫₀¹ f`. -/
