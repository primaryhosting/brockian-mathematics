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

open MeasureTheory SchwartzMap Real
open scoped FourierTransform ComplexInnerProductSpace

namespace QPhys

/-- **Plancherel/Parseval theorem**: the Fourier transform is an isometry of `L²`.

Here `𝓕` denotes the Fourier transform on `L²(ℝ, ℂ)` (with respect to Lebesgue measure),
and the statement says that it preserves the `L²` norm. -/

theorem parseval_fourier (f : Lp (α := ℝ) ℂ 2) : ‖𝓕 f‖ = ‖f‖ :=
  MeasureTheory.Lp.norm_fourier_eq f

/-- Polarized form of Parseval's identity: the Fourier transform on `L²(ℝ, ℂ)` preserves
the inner product. -/
