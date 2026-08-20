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

theorem dephase_isCPTP : IsCPTP (n := n) dephase := by
  refine ⟨n, inferInstance, fun i => Matrix.single i i 1, ?_, ?_⟩
  · have h : ∀ i : n, (Matrix.single i i (1 : ℂ))ᴴ * Matrix.single i i 1
        = Matrix.diagonal (Pi.single i (1 : ℂ)) := by
      intro i
      rw [single_eq_diagonal, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
      congr 1
      funext a
      by_cases h : i = a <;> simp [Pi.single_apply, h]
    rw [Finset.sum_congr rfl (fun i _ => h i)]
    ext a b
    rw [Matrix.sum_apply]
    by_cases hab : a = b
    · subst hab
      simp [Pi.single_apply, Finset.sum_ite_eq]
    · simp [hab]
  · intro X
    have h : ∀ i : n, Matrix.single i i (1 : ℂ) * X * (Matrix.single i i (1 : ℂ))ᴴ
        = Matrix.diagonal (Pi.single i (1 : ℂ)) * X * Matrix.diagonal (Pi.single i (1 : ℂ)) := by
      intro i
      rw [single_eq_diagonal, Matrix.diagonal_conjTranspose]
      congr 2
      funext a
      by_cases h : i = a <;> simp [Pi.single_apply, h]
    rw [Finset.sum_congr rfl (fun i _ => h i)]
    ext a b
    rw [Matrix.sum_apply]
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, dephase, Matrix.diagonal_apply,
      Pi.single_apply]
    by_cases hab : a = b
    · subst hab
      simp [Finset.sum_ite_eq]
    · simp [hab]

