/-
# Qft Unitary 3
Category: Quantum Computing
Target: QC.qft_unitary_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Qft Unitary 3
Category: Quantum Computing
Target: QC.qft_unitary_3
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QC

open Complex Matrix

/-- The primitive `8`-th root of unity `ω = e^{2πi/8}` used by the 3-qubit QFT. -/

lemma sum_pow_eight (w : ℂ) (hw : w ^ 8 = 1) :
    ∑ l : Fin 8, w ^ (l : ℕ) = if w = 1 then 8 else 0 := by
  by_cases h : w = 1
  · simp [h]
  · rw [if_neg h, Fin.sum_univ_eq_sum_range (fun i => w ^ i) 8, geom_sum_eq h, hw]
    simp

/-- The 3-qubit quantum Fourier transform matrix:
`(QFT₃)_{j,k} = ω^{jk} / √8` with `ω = e^{2πi/8}`. -/
