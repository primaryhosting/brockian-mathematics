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

theorem unitary_conj_isCPTP (u : unitary (Matrix n n ℂ)) :
    IsCPTP (fun X : Matrix n n ℂ => (u : Matrix n n ℂ) * X * star (u : Matrix n n ℂ)) := by
  refine ⟨PUnit, inferInstance, fun _ => (u : Matrix n n ℂ), ?_, ?_⟩
  · simpa [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self u
  · intro X
    simp [Matrix.star_eq_conjTranspose]

omit [Fintype n] in
