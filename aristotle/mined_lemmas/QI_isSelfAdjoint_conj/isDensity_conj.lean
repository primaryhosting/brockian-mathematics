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

theorem isDensity_conj (u : unitary (Matrix n n ℂ)) {ρ : Matrix n n ℂ} (hρ : IsDensity ρ) :
    IsDensity ((u : Matrix n n ℂ) * ρ * star (u : Matrix n n ℂ)) := by
  obtain ⟨hpd, htr⟩ := hρ
  refine ⟨?_, ?_⟩
  · have hu : IsUnit (u : Matrix n n ℂ) := IsUnit.of_mul_eq_one _ (Unitary.coe_mul_star_self u)
    rw [Matrix.star_eq_conjTranspose]
    exact hpd.mul_mul_conjTranspose_same (Matrix.vecMul_injective_of_isUnit hu)
  · rw [trace_conj_eq, htr]

/-- Measurement in the orthonormal basis formed by the columns of a unitary `u`: the completely
dephasing channel conjugated by `u`. -/
