import Mathlib

/-!
# Parseval Fourier
Category: Quantum Physics
Target: QPhys.parseval_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Note: Lean 4 requires `import` statements to come first in a file, so the header
module docstring above is placed immediately after the single `import Mathlib` line.
-/

open scoped BigOperators
open scoped Real
open scoped FourierTransform
open scoped ComplexInnerProductSpace

open MeasureTheory SchwartzMap

noncomputable section

namespace QPhys

/-- The one-dimensional Fourier transform of a wave function, written with the explicit
oscillatory kernel `e^{-2πi x p}` used in physics:
`(𝓕 ψ)(p) = ∫ e^{-2 π i x p} ψ(x) dx`. -/

theorem parseval_fourier_L2_inner (f g : Lp (α := ℝ) ℂ 2) :
    ⟪(𝓕 f : Lp (α := ℝ) ℂ 2), (𝓕 g : Lp (α := ℝ) ℂ 2)⟫ = ⟪f, g⟫ :=
  MeasureTheory.Lp.inner_fourier_eq f g

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

