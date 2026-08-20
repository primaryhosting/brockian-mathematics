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

theorem dephase_trace_selfAdjoint (X Y : Matrix n n ℂ) :
    Matrix.trace (dephase X * Y) = Matrix.trace (X * dephase Y) := by
  simp [dephase, Matrix.trace, Matrix.mul_apply, Matrix.diagonal, Finset.sum_ite_eq,
    apply_ite, mul_comm]

omit [Fintype n] [DecidableEq n] in
/-- A positive definite matrix has real positive diagonal entries. -/
