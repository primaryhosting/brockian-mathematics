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

theorem normSq_row_sum (M : Matrix n n ℂ) (h : M * star M = 1) (i : n) :
    ∑ j, Complex.normSq (M i j) = 1 := by
  have h2 := congrFun (congrFun h i) i
  rw [Matrix.mul_apply] at h2
  simp only [Matrix.star_apply, RCLike.star_def, Matrix.one_apply_eq] at h2
  have h3 : ∀ j : n, M i j * (starRingEnd ℂ) (M i j) = ((Complex.normSq (M i j) : ℝ) : ℂ) :=
    fun j => Complex.mul_conj _
  rw [Finset.sum_congr rfl (fun j _ => h3 j)] at h2
  exact_mod_cast h2

/-- The column sums of the doubly stochastic matrix `|M i j|²` of a unitary `M`. -/
