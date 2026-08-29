/-
# Qft Unitary 2
Category: Quantum Computing
Target: QC.qft_unitary_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary 2
Category: Quantum Computing
Target: QC.qft_unitary_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

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

/-- The 2-qubit quantum Fourier transform matrix: the `4 × 4` matrix with entries
`(1 / √4) * exp (2 π i j k / 4)`. -/

lemma qft2_eq_explicit :
    qft2 = (1 / 2 : ℂ) • !![1, 1, 1, 1;
                            1, Complex.I, -1, -Complex.I;
                            1, -1, 1, -1;
                            1, -Complex.I, -1, Complex.I] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qft2_apply, pow_succ]

/-- `qft2ᴴ * qft2 = 1`. -/
