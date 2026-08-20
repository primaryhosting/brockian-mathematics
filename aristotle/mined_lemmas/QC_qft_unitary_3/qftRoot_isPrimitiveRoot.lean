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

/-- The `N × N` discrete Fourier transform (QFT) matrix:
`(QFT)_{j,k} = (1/√N) · exp(2πi·j·k/N)`. -/

lemma qftRoot_isPrimitiveRoot (N : ℕ) (hN : N ≠ 0) : IsPrimitiveRoot (qftRoot N) N := by
  have := Complex.isPrimitiveRoot_exp N hN
  simpa [qftRoot, mul_comm, mul_assoc, mul_left_comm] using this

