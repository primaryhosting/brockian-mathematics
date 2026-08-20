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

theorem le_chi {t : ℝ} (ht : 0 < t) {P Q : Matrix n n ℂ} (hP : P.PosDef) (hQ : Q.PosDef)
    (Y : Matrix n n ℂ) :
    2 * (Matrix.trace (Yᴴ * (P - Q))).re - quadForm t P Q Y ≤ chi t hP.1 hQ.1 := by
  have h0 : 0 ≤ quadForm t P Q (Y - sylv t hP.1 hQ.1) :=
    quadForm_nonneg ht.le hP.posSemidef hQ.posSemidef _
  have hexp := quadForm_sub t hP.1 hQ.1 Y (sylv t hP.1 hQ.1)
  rw [pairing_sylv ht hP hQ Y, quadForm_sylv ht hP hQ] at hexp
  linarith

/-- The variational bound is attained at the solution of the Sylvester equation. -/
