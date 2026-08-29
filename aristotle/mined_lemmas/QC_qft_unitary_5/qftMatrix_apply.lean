/-
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
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

open Complex Matrix

/-- The primitive `n`-th root of unity `exp (2 π i / n)`. -/

lemma qftMatrix_apply (n : ℕ) (j k : Fin n) :
    qftMatrix n j k =
      ((Real.sqrt n : ℝ) : ℂ)⁻¹ *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j.val * k.val) / n) := by
  unfold qftMatrix qftOmega
  simp only [Matrix.of_apply]
  rw [← Complex.exp_nat_mul]
  push_cast
  ring_nf

