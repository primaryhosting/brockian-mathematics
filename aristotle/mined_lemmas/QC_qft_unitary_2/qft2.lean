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

/-- The 2-qubit quantum Fourier transform matrix, acting on the 4-dimensional state space.
Its `(j, k)` entry is `(1/2) * ω ^ (j * k)` where `ω = exp(2 * π * I / 4) = I` is a primitive
4-th root of unity. -/

noncomputable def qft2 : Matrix (Fin 4) (Fin 4) ℂ :=
  fun j k => (1 / 2 : ℂ) * Complex.I ^ ((j : ℕ) * (k : ℕ))

/-- The normalization constant `1/2` is `1/√(2^2)`, and `I = exp(2πI/4)` is the primitive
4-th root of unity used by the 2-qubit QFT. -/
