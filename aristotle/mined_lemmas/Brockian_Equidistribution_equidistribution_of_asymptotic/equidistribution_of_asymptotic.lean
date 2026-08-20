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
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Filter Topology AddCircle

namespace Brockian.Equidistribution

/-- The Cesàro (Birkhoff) average of `f` along the first `N` terms of the sequence `x`. -/

theorem equidistribution_of_asymptotic (x : ℕ → AddCircle (1 : ℝ))
    (hx : ∀ k : ℤ, k ≠ 0 → Tendsto (cesaroAvg x (fourier k)) atTop (𝓝 0))
    (f : C(AddCircle (1 : ℝ), ℂ)) :
    Tendsto (cesaroAvg x f) atTop (𝓝 (∫ t, f t ∂(haarAddCircle (T := 1)))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, hgmem, hgdist⟩ := exists_mem_span_dist_lt f (by positivity : (0 : ℝ) < ε / 3)
  have hg := tendsto_cesaroAvg_of_mem_span x hx g hgmem
  rw [Metric.tendsto_atTop] at hg
  obtain ⟨N₀, hN₀⟩ := hg (ε / 3) (by positivity)
  refine ⟨N₀, fun N hN => ?_⟩
  have h1 : ‖cesaroAvg x f N - cesaroAvg x g N‖ < ε / 3 := by
    rw [← cesaroAvg_sub]
    exact lt_of_le_of_lt (norm_cesaroAvg_le x (f - g) N) (by
      rwa [← NormedAddGroup.dist_eq])
  have h2 : dist (cesaroAvg x g N) (∫ t, g t ∂(haarAddCircle (T := 1))) < ε / 3 := hN₀ N hN
  have h3 : ‖(∫ t, g t ∂(haarAddCircle (T := 1))) - ∫ t, f t ∂(haarAddCircle (T := 1))‖
      < ε / 3 := by
    rw [← integral_sub (integrable_continuous g) (integrable_continuous f)]
    refine lt_of_le_of_lt ?_ (by rwa [← NormedAddGroup.dist_eq, dist_comm] :
      ‖g - f‖ < ε / 3)
    simpa using norm_integral_le (g - f)
  calc dist (cesaroAvg x f N) (∫ t, f t ∂(haarAddCircle (T := 1)))
      ≤ dist (cesaroAvg x f N) (cesaroAvg x g N)
        + dist (cesaroAvg x g N) (∫ t, g t ∂(haarAddCircle (T := 1)))
        + dist (∫ t, g t ∂(haarAddCircle (T := 1))) (∫ t, f t ∂(haarAddCircle (T := 1))) := by
        exact dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        rw [dist_eq_norm, dist_eq_norm (∫ t, g t ∂(haarAddCircle (T := 1)))]
        exact add_lt_add (add_lt_add h1 h2) h3
    _ = ε := by ring

/-!
### An unconditional application: irrational rotations

The hypothesis of `equidistribution_of_asymptotic` is verified for the orbit `n ↦ n * a`
of an irrational rotation, which yields Weyl's equidistribution theorem for `(n a)` unconditionally.
-/

/-- For irrational `a` and a nonzero frequency `k`, the exponential sums along the orbit
`n ↦ n * a` of the irrational rotation tend to zero (geometric sum bound). -/
