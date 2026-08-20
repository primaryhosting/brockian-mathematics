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

theorem data_processing_condExp {E : Matrix n n ℂ → Matrix n n ℂ} {ρ σ : Matrix n n ℂ}
    (hsa : ∀ X Y, Matrix.trace (E X * Y) = Matrix.trace (X * E Y))
    (hρ : IsDensity ρ) (hEρ : IsDensity (E ρ))
    (hEσ : E σ = σ) (hlogσ : E (logM σ) = logM σ) (hlogEρ : E (logM (E ρ)) = logM (E ρ)) :
    relEntropy (E ρ) (E σ) ≤ relEntropy ρ σ := by
  have h1 : Matrix.trace (E ρ * logM (E ρ)) = Matrix.trace (ρ * logM (E ρ)) := by
    rw [hsa ρ (logM (E ρ)), hlogEρ]
  have h2 : Matrix.trace (E ρ * logM σ) = Matrix.trace (ρ * logM σ) := by
    rw [hsa ρ (logM σ), hlogσ]
  have hklein : (0 : ℝ) ≤ (Matrix.trace (ρ * logM ρ)).re - (Matrix.trace (ρ * logM (E ρ))).re :=
    relEntropy_nonneg hρ hEρ
  rw [hEσ, relEntropy, h1, h2, relEntropy]
  linarith

/-! ### The completely dephasing channel -/

/-- The completely dephasing channel in the computational basis: it keeps the diagonal of a
matrix and erases all off-diagonal entries. -/
