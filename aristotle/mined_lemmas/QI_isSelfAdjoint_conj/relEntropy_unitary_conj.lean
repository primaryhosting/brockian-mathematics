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

theorem relEntropy_unitary_conj (u : unitary (Matrix n n ℂ)) {ρ σ : Matrix n n ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    relEntropy ((u : Matrix n n ℂ) * ρ * star (u : Matrix n n ℂ))
      ((u : Matrix n n ℂ) * σ * star (u : Matrix n n ℂ)) = relEntropy ρ σ := by
  have hρ' : IsSelfAdjoint ρ := hρ
  have hσ' : IsSelfAdjoint σ := hσ
  have hlρ : logM ((u : Matrix n n ℂ) * ρ * star (u : Matrix n n ℂ))
      = (u : Matrix n n ℂ) * logM ρ * star (u : Matrix n n ℂ) := cfc_conj_unitary _ _ hρ'
  have hlσ : logM ((u : Matrix n n ℂ) * σ * star (u : Matrix n n ℂ))
      = (u : Matrix n n ℂ) * logM σ * star (u : Matrix n n ℂ) := cfc_conj_unitary _ _ hσ'
  rw [relEntropy, relEntropy, hlρ, hlσ, conj_mul_conj, conj_mul_conj, trace_conj_eq,
    trace_conj_eq]

/-! ### Data processing -/

/-- **Data processing inequality** for a trace-self-adjoint map `E` (a conditional expectation)
which fixes `σ`, together with the logarithms occurring in the statement. -/
