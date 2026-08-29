import Mathlib

/-!
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
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

namespace QC

/-- The primitive 16-th root of unity `exp (2πi/16)`. -/

lemma qft4_apply (j k : Fin 16) :
    qft4 j k = Complex.exp (2 * Real.pi * Complex.I * (j.val * k.val) / 16) / 4 := by
  rw [qft4, zeta16, ← Complex.exp_nat_mul]
  norm_num
  congr 1
  ring

/-- Explicit form of unitarity: `QFT^† * QFT = 1`. -/
