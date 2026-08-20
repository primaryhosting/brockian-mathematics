/-
# Carleson
Category: Frontier Math
Target: Math2.carleson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 does not allow a module docstring before the import line, so the
required header is reproduced here as a plain comment and again as a module
docstring immediately after the import.)
-/

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math2

open MeasureTheory Filter Topology
open scoped ENNReal

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The `N`-th symmetric partial sum of the Fourier series of `f` at the point `x`. -/

lemma tendsto_fourierPartialSumLp (f : Lp ℂ 2 (@AddCircle.haarAddCircle T hT)) :
    Tendsto (fourierPartialSumLp f) atTop (𝓝 f) := by
  have h : Tendsto (fun s : Finset ℤ =>
      ∑ n ∈ s, fourierCoeff (⇑f) n • fourierLp (T := T) 2 n) atTop (𝓝 f) := by
    simpa only [fourierBasis_repr] using hasSum_fourier_series_L2 f
  exact h.comp tendsto_Icc_atTop

/-- The `L²`-valued partial sum agrees almost everywhere with the pointwise partial sum. -/
