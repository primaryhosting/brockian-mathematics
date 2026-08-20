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

theorem trace_conj_diag_mul_conj_diag (u v : unitary (Matrix n n ℂ)) (a b : n → ℝ) :
    Matrix.trace (((u : Matrix n n ℂ) * Matrix.diagonal (fun i => (a i : ℂ))
        * star (u : Matrix n n ℂ)) *
        ((v : Matrix n n ℂ) * Matrix.diagonal (fun i => (b i : ℂ))
        * star (v : Matrix n n ℂ)))
      = ((∑ i, ∑ j, a i * b j *
          Complex.normSq ((star (u : Matrix n n ℂ) * (v : Matrix n n ℂ)) i j) : ℝ) : ℂ) := by
  set U := (u : Matrix n n ℂ) with hUdef
  set V := (v : Matrix n n ℂ) with hVdef
  set A := Matrix.diagonal (fun i => (a i : ℂ)) with hA
  set B := Matrix.diagonal (fun i => (b i : ℂ)) with hB
  set M := star U * V with hM
  have e1 : U * A * star U * (V * B * star V) = U * (A * star U * V * B * star V) := by
    noncomm_ring
  have e2 : A * star U * V * B * star V * U = A * M * B * star M := by
    rw [hM, Matrix.star_mul, star_star]
    noncomm_ring
  have e4 : ∀ i j, (A * M * B) i j = (a i : ℂ) * M i j * (b j : ℂ) := by
    intro i j
    rw [hA, hB, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [e1, Matrix.trace_mul_comm, e2, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, e4, Matrix.star_apply, RCLike.star_def]
  push_cast [← Complex.mul_conj]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The row sums of the doubly stochastic matrix `|M i j|²` of a unitary `M`. -/
