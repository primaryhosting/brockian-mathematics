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

theorem fourierCoeff_sub (hf : Integrable f haarAddCircle) (hg : Integrable g haarAddCircle)
    (n : ℤ) : fourierCoeff (fun y => f y - g y) n = fourierCoeff f n - fourierCoeff g n := by
  have h1 : (fun y => f y - g y) = f + (fun y => (-1 : ℂ) * g y) := by
    funext y; simp [sub_eq_add_neg]
  have h2 : Integrable (fun y => (-1 : ℂ) * g y) haarAddCircle := hg.const_mul _
  rw [h1, fourierCoeff.add hf h2, Pi.add_apply, fourierCoeff.const_mul g (-1) n]
  ring

/-- Linearity of the partial sums with respect to `f`. -/
