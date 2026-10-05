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

noncomputable def fourierPartialSum {T : ℝ} [Fact (0 < T)] (f : AddCircle T → ℂ) (N : ℕ)
    (x : AddCircle T) : ℂ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), fourierCoeff f n * fourier n x

section Aux

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The coercion to a function of a finite sum in `Lp` is a.e. the pointwise finite sum. -/
