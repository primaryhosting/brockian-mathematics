import Mathlib

/-!
# Quantum relative entropy and data processing

This file develops, for finite-dimensional systems (complex matrices), the basic theory of the
Umegaki quantum relative entropy

`D(ρ‖σ) = Tr(ρ log ρ) - Tr(ρ log σ)`

for faithful (positive definite) density matrices, together with

* Klein's inequality `QI.relEntropy_nonneg` : `0 ≤ D(ρ‖σ)`;
* invariance under unitary channels `QI.relEntropy_unitary_conj`;
* the data-processing inequality `QI.data_processing_condExp` for trace-self-adjoint maps fixing `σ`
  (conditional expectations), and its concrete instance for the completely dephasing channel
  `QI.data_processing_dephasing`.
-/

open Matrix
open scoped ComplexOrder

namespace QI

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- The logarithm of a (Hermitian) matrix, defined through the continuous functional calculus. -/

theorem pairing_sylv {t : ℝ} (ht : 0 < t) {P Q : Matrix n n ℂ} (hP : P.PosDef) (hQ : Q.PosDef)
    (Y : Matrix n n ℂ) :
    t * (Matrix.trace (Yᴴ * (P * sylv t hP.1 hQ.1))).re
        + (Matrix.trace (Yᴴ * (sylv t hP.1 hQ.1 * Q))).re
      = (Matrix.trace (Yᴴ * (P - Q))).re := by
  have hsyl := sylv_sylvester ht hP hQ
  have h : Matrix.trace (Yᴴ * (P - Q))
      = (t : ℂ) * Matrix.trace (Yᴴ * (P * sylv t hP.1 hQ.1))
        + Matrix.trace (Yᴴ * (sylv t hP.1 hQ.1 * Q)) := by
    rw [← hsyl, Matrix.mul_add, Matrix.trace_add, Matrix.mul_smul, Matrix.trace_smul,
      smul_eq_mul]
  rw [h]
  simp [Complex.add_re]

/-- The value of the quadratic form at the Sylvester solution is `χ_t`. -/
