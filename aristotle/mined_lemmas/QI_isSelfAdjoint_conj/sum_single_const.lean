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

theorem sum_single_const {m : Type u} [Fintype m] (i : n) (f : m → ℂ) :
    ∑ j, Matrix.single i i (f j) = Matrix.single i i (∑ j, f j) := by
  ext a b
  rw [Matrix.sum_apply]
  simp only [Matrix.single_apply]
  by_cases h : i = a ∧ i = b <;> simp [h]

/-- The measure-and-prepare channel attached to a column-stochastic matrix `T`: measure in the
computational basis, then prepare the classical state obtained by pushing the outcome
distribution through `T`. -/
