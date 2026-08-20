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

theorem trace_krausMap_mul {ι : Type u} [Fintype ι] (K : ι → Matrix m n ℂ) (X : Matrix n n ℂ)
    (Y : Matrix m m ℂ) :
    Matrix.trace (krausMap K X * Y) = Matrix.trace (X * krausAdj K Y) := by
  simp only [krausMap, krausAdj, Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, Matrix.mul_assoc X]

omit [DecidableEq m] in
/-- **Kadison-Schwarz inequality** for the adjoint of a trace preserving Kraus channel. -/
