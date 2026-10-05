import Mathlib

/-!
# Carleson
Category: Frontier Math
Target: Math2.carleson
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

namespace Math2

open MeasureTheory Filter Topology AddCircle

/-- The `N`-th symmetric partial sum of the Fourier series of `f : AddCircle T → ℂ`,
i.e. `∑_{|n| ≤ N} (fourierCoeff f n) * e^{2πinx/T}`. -/

theorem tendsto_fourierPartialSum_of_summable {T : ℝ} [hT : Fact (0 < T)]
    {f : C(AddCircle T, ℂ)} (h : Summable (fourierCoeff (⇑f))) (x : AddCircle T) :
    Tendsto (fun N : ℕ => fourierPartialSum (⇑f) N x) atTop (𝓝 (f x)) := by
  have hs := (has_pointwise_sum_fourier_series_of_summable h x).comp tendsto_Icc_atTop
  simpa [fourierPartialSum, Function.comp_def, smul_eq_mul] using hs

/-
For the record, the full strength of Carleson's theorem is the following statement, in which the
whole sequence of partial sums (not merely a subsequence) converges almost everywhere:

