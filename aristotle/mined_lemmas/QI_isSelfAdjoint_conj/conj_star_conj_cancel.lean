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

theorem conj_star_conj_cancel (u : unitary (Matrix n n ℂ)) (X : Matrix n n ℂ) :
    (u : Matrix n n ℂ) * (star (u : Matrix n n ℂ) * X * (u : Matrix n n ℂ))
      * star (u : Matrix n n ℂ) = X := by
  have hsu : (u : Matrix n n ℂ) * star (u : Matrix n n ℂ) = 1 := Unitary.coe_mul_star_self u
  simp only [← mul_assoc]
  rw [hsu, one_mul, mul_assoc, hsu, mul_one]

/-- Conjugation by a unitary maps faithful states to faithful states. -/
