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

theorem trace_mul_logM_re {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    (Matrix.trace (ρ * logM σ)).re
      = ∑ i, ∑ j, hρ.eigenvalues i * Real.log (hσ.eigenvalues j) *
          Complex.normSq ((star (hρ.eigenvectorUnitary : Matrix n n ℂ)
            * (hσ.eigenvectorUnitary : Matrix n n ℂ)) i j) := by
  have h : Matrix.trace (ρ * logM σ)
      = ((∑ i, ∑ j, hρ.eigenvalues i * Real.log (hσ.eigenvalues j) *
          Complex.normSq ((star (hρ.eigenvectorUnitary : Matrix n n ℂ)
            * (hσ.eigenvectorUnitary : Matrix n n ℂ)) i j) : ℝ) : ℂ) := by
    conv_lhs => rw [logM_of_isHermitian hσ, spectral_decomp hρ]
    exact trace_conj_diag_mul_conj_diag _ _ _ _
  rw [h, Complex.ofReal_re]

