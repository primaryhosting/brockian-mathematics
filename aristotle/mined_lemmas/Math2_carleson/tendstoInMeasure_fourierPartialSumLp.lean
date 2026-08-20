/-
# Carleson
Category: Frontier Math
Target: Math2.carleson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Math2

open MeasureTheory Filter Topology AddCircle

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The symmetric partial sum of the Fourier series of `f` at `x`:
`∑_{n = -N}^{N} (fourierCoeff f n) e^{2πinx/T}`. -/

lemma tendstoInMeasure_fourierPartialSumLp (f : Lp ℂ 2 (@haarAddCircle T hT)) :
    TendstoInMeasure (@haarAddCircle T hT)
      (fun N : ℕ => (fourierPartialSumLp f N : AddCircle T → ℂ)) atTop
      (f : AddCircle T → ℂ) :=
  tendstoInMeasure_of_tendsto_Lp (tendsto_fourierPartialSumLp f)

/-- **Convergence in measure of Fourier series of `L²` functions** (whole sequence):
the symmetric partial Fourier sums of an `L²` function on the circle converge to it in
measure. -/
