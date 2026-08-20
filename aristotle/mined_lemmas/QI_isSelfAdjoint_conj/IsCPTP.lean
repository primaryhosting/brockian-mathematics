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

def IsCPTP {m : Type u} [Fintype m] [DecidableEq m]
    (Φ : Matrix n n ℂ → Matrix m m ℂ) : Prop :=
  ∃ (ι : Type u) (_ : Fintype ι) (K : ι → Matrix m n ℂ),
    (∑ a, (K a)ᴴ * K a = 1) ∧ ∀ X, Φ X = ∑ a, K a * X * (K a)ᴴ

omit [Fintype n] in
