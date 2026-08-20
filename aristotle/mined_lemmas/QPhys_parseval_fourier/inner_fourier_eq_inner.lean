/-
# Parseval Fourier
Category: Quantum Physics
Target: QPhys.parseval_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open MeasureTheory FourierTransform ComplexInnerProductSpace

namespace QPhys

/-- For an `L²` function `f : ℝ → ℂ` (a one–dimensional wavefunction), the integral of `‖f‖²`
is the square of its `L²` norm. -/

theorem inner_fourier_eq_inner (f g : Lp (α := ℝ) ℂ 2) :
    ⟪𝓕 f, 𝓕 g⟫ = ⟪f, g⟫ :=
  Lp.inner_fourier_eq f g

end QPhys

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

