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

theorem relEntropy_diagonal (p q : n → ℝ) :
    relEntropy (Matrix.diagonal (fun i => (p i : ℂ))) (Matrix.diagonal (fun i => (q i : ℂ)))
      = ∑ i, p i * (Real.log (p i) - Real.log (q i)) := by
  rw [relEntropy, logM, logM, cfc_diagonal, cfc_diagonal, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Matrix.trace_diagonal]
  have h1 : ∑ i, ((p i : ℂ) * (Real.log (p i) : ℂ)) = ((∑ i, p i * Real.log (p i) : ℝ) : ℂ) := by
    push_cast; ring
  have h2 : ∑ i, ((p i : ℂ) * (Real.log (q i) : ℂ)) = ((∑ i, p i * Real.log (q i) : ℝ) : ℂ) := by
    push_cast; ring
  rw [h1, h2, Complex.ofReal_re, Complex.ofReal_re, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

