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

theorem sum_single_diag (d : n → ℂ) : ∑ i, Matrix.single i i (d i) = Matrix.diagonal d := by
  ext a b
  rw [Matrix.sum_apply]
  simp only [Matrix.single_apply, Matrix.diagonal_apply]
  by_cases hab : a = b
  · subst hab
    simp [Finset.sum_ite_eq, eq_comm]
  · rw [if_neg hab]
    exact Finset.sum_eq_zero fun i _ => if_neg (by rintro ⟨rfl, rfl⟩; exact hab rfl)

omit [Fintype n] in
