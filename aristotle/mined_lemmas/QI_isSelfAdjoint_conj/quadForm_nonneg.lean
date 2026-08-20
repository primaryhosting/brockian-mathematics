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

theorem quadForm_nonneg {t : ℝ} (ht : 0 ≤ t) {P Q : Matrix n n ℂ} (hP : P.PosSemidef)
    (hQ : Q.PosSemidef) (Y : Matrix n n ℂ) : 0 ≤ quadForm t P Q Y := by
  have h1 : (Matrix.trace (Yᴴ * P * Y)).re = (Matrix.trace (P * (Y * Yᴴ))).re := by
    congr 1
    rw [Matrix.trace_mul_cycle, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  have h2 : (Matrix.trace (Yᴴ * Y * Q)).re = (Matrix.trace (Q * (Yᴴ * Y))).re := by
    congr 1
    rw [Matrix.trace_mul_comm]
  rw [quadForm, h1, h2]
  have p1 := trace_mul_posSemidef_nonneg hP (Matrix.posSemidef_self_mul_conjTranspose Y)
  have p2 := trace_mul_posSemidef_nonneg hQ (Matrix.posSemidef_conjTranspose_mul_self Y)
  have := mul_nonneg ht p1
  linarith

omit [DecidableEq n] in
/-- Expansion of the quadratic form along a difference. -/
