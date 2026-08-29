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

/-- The primitive 8-th root of unity `exp (2 π i / 8)`. -/

lemma term_eq (j k l : Fin 8) :
    (star qft3) j l * qft3 l k = (omega8 ^ (7 * j.val + k.val)) ^ (l : ℕ) / 8 := by
  have hstar : (star qft3) j l = omega8 ^ (7 * (l.val * j.val)) / (Real.sqrt 8 : ℝ) := by
    rw [Matrix.star_apply]
    simp only [qft3, Matrix.of_apply, star_div', star_pow, Complex.star_def,
      Complex.conj_ofReal, conj_omega8, ← pow_mul]
    congr 1
    ring
  rw [hstar]
  simp only [qft3, Matrix.of_apply]
  rw [div_mul_div_comm, sqrt_eight_sq, ← pow_add, ← pow_mul]
  congr 2
  ring

