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

theorem quadForm_sub (t : ℝ) {P Q : Matrix n n ℂ} (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (Y W : Matrix n n ℂ) :
    quadForm t P Q (Y - W) = quadForm t P Q Y
      - 2 * (t * (Matrix.trace (Yᴴ * (P * W))).re + (Matrix.trace (Yᴴ * (W * Q))).re)
      + quadForm t P Q W := by
  unfold quadForm
  have e1 : (Y - W)ᴴ * P * (Y - W) = Yᴴ * P * Y - Yᴴ * P * W - Wᴴ * P * Y + Wᴴ * P * W := by
    simp only [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub]; abel
  have e2 : (Y - W)ᴴ * (Y - W) * Q = Yᴴ * Y * Q - Yᴴ * W * Q - Wᴴ * Y * Q + Wᴴ * W * Q := by
    simp only [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub]; abel
  have c1 : (Matrix.trace (Wᴴ * (P * Y))).re = (Matrix.trace (Yᴴ * (P * W))).re := by
    rw [trace_conjT_re W (P * Y), Matrix.conjTranspose_mul, hP.eq, Matrix.mul_assoc]
  have c2 : (Matrix.trace (Wᴴ * (Y * Q))).re = (Matrix.trace (Yᴴ * (W * Q))).re := by
    rw [trace_conjT_re W (Y * Q), Matrix.conjTranspose_mul, hQ.eq]
    congr 1
    rw [Matrix.trace_mul_cycle, Matrix.trace_mul_cycle, Matrix.mul_assoc]
  rw [e1, e2]
  simp only [Matrix.trace_add, Matrix.trace_sub, Complex.add_re, Complex.sub_re, Matrix.mul_assoc]
  rw [c1, c2]
  ring

/-- The bilinear pairing of an arbitrary `Y` with the Sylvester solution. -/
