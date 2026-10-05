/-
# Qft Unitary 8
Category: Quantum Computing
Target: QC.qft_unitary_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Complex Matrix Finset

namespace QC

/-- The `n × n` quantum Fourier transform matrix: the entry at `(j, k)` is
`ω^(j*k) / √n`, where `ω = exp(2πi/n)` is a primitive `n`-th root of unity. -/

theorem qft_unitary_256 : qftMatrix 256 ∈ Matrix.unitaryGroup (Fin 256) ℂ :=
  Matrix.mem_unitaryGroup_iff.mpr (qft_mul_conjTranspose 256 (by norm_num))

end QC

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

