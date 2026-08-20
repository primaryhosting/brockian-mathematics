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

lemma qftMatrix_apply (N : ℕ) (j k : Fin N) :
    qftMatrix N j k = ((Real.sqrt N : ℝ) : ℂ)⁻¹ * (qftRoot N) ^ ((j : ℕ) * (k : ℕ)) := by
  rw [qftMatrix]
  simp only [Matrix.of_apply]
  rw [qftRoot, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

