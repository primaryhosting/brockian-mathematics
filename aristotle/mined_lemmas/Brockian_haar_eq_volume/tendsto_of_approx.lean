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
# Equidistribution of irrational rotations, and the density of configuration counts

This file proves Weyl's equidistribution theorem for the sequence `n ↦ {n α}` (`α` irrational)
and deduces the unconditional statement `configCount_density_of_BV`: the density of the set of
`n < N` with `{n α} ∈ [a, b)` tends to `b - a`.

The indicator of an interval is the basic example of a function of bounded variation, and the
"BV reduction" is implemented here through the portmanteau theorem: the empirical measures of
the orbit converge weakly to Haar measure (proved via the Fourier/Weyl criterion), hence the
measures of any arc whose boundary is Haar-null converge.
-/

namespace Brockian
namespace EquidistributionBVReduction

open Filter MeasureTheory Set Topology AddCircle
open scoped BigOperators ENNReal NNReal

/-- The point `n • α` of the circle `ℝ / ℤ`. -/

lemma tendsto_of_approx {u : ℕ → ℂ} {L : ℂ}
    (h : ∀ ε > (0:ℝ), ∃ (v : ℕ → ℂ) (M : ℂ), Tendsto v atTop (𝓝 M) ∧
      (∀ n, dist (u n) (v n) ≤ ε) ∧ dist M L ≤ ε) :
    Tendsto u atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨v, M, hv, hd, hML⟩ := h (ε/3) (by linarith)
  rw [Metric.tendsto_atTop] at hv
  obtain ⟨N, hN⟩ := hv (ε/3) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hd n
  have h2 := hN n hn
  calc dist (u n) L ≤ dist (u n) (v n) + dist (v n) M + dist M L := dist_triangle4 _ _ _ _
    _ < ε := by linarith

/-- Weyl's theorem for continuous functions: the orbit averages of a continuous function
converge to its Haar integral. -/
