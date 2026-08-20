import Mathlib

/-!
# Carleson
Category: Frontier Math
Target: Math2.carleson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
## Contents

`Math2.carleson` : the Fourier series of a square-integrable function on the circle
`AddCircle 1` converges to it almost everywhere.  The statement takes as an explicit hypothesis
the key intermediate result `Math2.CarlesonWeakL2 C`, the Carleson-Hunt weak `(2,2)` maximal
inequality for the Carleson maximal operator; everything else -- the density/approximation
argument by trigonometric polynomials and the passage from the maximal inequality to almost
everywhere convergence -- is proved here from scratch.

Proved unconditionally (no hypothesis) in this file:

* `Math2.tendsto_eLpNorm_partialFourierSum` : `L²` convergence of the partial Fourier sums;
* `Math2.exists_subseq_ae_tendsto_partialFourierSum` : almost everywhere convergence of a
  subsequence of the partial Fourier sums.
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

open MeasureTheory AddCircle Filter Topology

noncomputable section

/-- The `N`-th symmetric partial sum of the Fourier series of `f : AddCircle 1 → ℂ`. -/

theorem tendsto_of_divergenceLimsup_eq_zero {f : AddCircle (1 : ℝ) → ℂ} {x : AddCircle (1 : ℝ)}
    (hx : divergenceLimsup f x = 0) :
    Tendsto (fun N => partialFourierSum f N x) atTop (𝓝 (f x)) := by
  have h1 : Tendsto (fun N => ‖partialFourierSum f N x - f x‖ₑ) atTop (𝓝 0) :=
    tendsto_of_le_liminf_of_limsup_le (a := (0 : ℝ≥0∞)) bot_le (le_of_eq hx)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h2 := (ENNReal.tendsto_toReal (a := (0 : ℝ≥0∞)) (by simp)).comp h1
  simpa [Function.comp] using h2

/-- **Carleson's theorem.**  The Fourier series of a square-integrable function on the circle
converges to it almost everywhere.

The proof is conditional on the key intermediate result `CarlesonWeakL2 C`, the Carleson–Hunt
weak `(2,2)` maximal inequality for the Carleson operator, which is supplied as a hypothesis. -/
