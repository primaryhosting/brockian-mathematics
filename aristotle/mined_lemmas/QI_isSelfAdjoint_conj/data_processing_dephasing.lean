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

theorem data_processing_dephasing {ρ σ : Matrix n n ℂ} (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (hdiag : dephase σ = σ) :
    relEntropy (dephase ρ) (dephase σ) ≤ relEntropy ρ σ := by
  have hEρ : IsDensity (dephase ρ) := isDensity_dephase hρ
  -- `σ` and `dephase ρ` are diagonal with positive entries, hence so are their logarithms
  have hlog_diag : ∀ τ : Matrix n n ℂ, IsDensity τ → dephase τ = τ → dephase (logM τ) = logM τ := by
    intro τ hτ hd
    have he : τ = Matrix.diagonal (fun i => (((τ i i).re : ℝ) : ℂ)) := by
      conv_lhs => rw [← hd]
      unfold dephase
      congr 1
      funext i
      exact (posDef_diag_re hτ.1 i).2
    rw [he, logM, cfc_diagonal, dephase_diagonal]
  have hlogσ := hlog_diag σ hσ hdiag
  have hlogEρ := hlog_diag (dephase ρ) hEρ (dephase_diagonal _)
  exact data_processing_condExp dephase_trace_selfAdjoint hρ hEρ hdiag hlogσ hlogEρ

/-! ### Measure-and-prepare (classical) channels -/

/-- The relative entropy of two diagonal states is the classical Kullback-Leibler divergence of
their diagonals. -/
