import Mathlib

/-!
# Total Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.total_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Brockian
namespace EquidistributionBVReduction

open Filter Finset

/-- The `N`-th equidistributed sample sum of `f`: the total of the values of `f` at the
`N` equidistributed sample points `0/N, 1/N, …, (N-1)/N` of the unit interval. -/

lemma sum_piece_integrals (hp : MonotoneOn p (Set.Icc (0:ℝ) 1)) {N : ℕ} (hN : 0 < N) :
    ∑ k ∈ Finset.range N, (∫ x in ((k : ℝ) / N)..(((k : ℝ) + 1) / N), p x)
      = ∫ x in (0:ℝ)..1, p x := by
  have h := intervalIntegral.sum_integral_adjacent_intervals (μ := MeasureTheory.volume)
    (a := fun k : ℕ => (k : ℝ) / N) (f := p) (n := N)
    (fun k hk => by simpa [Nat.cast_add] using intervalIntegrable_piece hp hk)
  have hN' : (N : ℝ) ≠ 0 := by positivity
  simpa [div_self hN'] using h

/-- Lower bound for the integral over one piece, by the left endpoint value. -/
