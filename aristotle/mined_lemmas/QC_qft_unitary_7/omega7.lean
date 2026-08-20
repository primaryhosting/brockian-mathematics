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

namespace QC

/-- The primitive `128`-th root of unity `exp (2 π i / 128)` used by the 7-qubit QFT. -/

noncomputable def omega7 : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (128 : ℕ))

/-- The 7-qubit quantum Fourier transform matrix, acting on the `2 ^ 7 = 128`
dimensional state space: its `(j, k)` entry is `exp (2 π i j k / 128) / √128`. -/
