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

theorem dephaseIn_eigenbasis_eq_self {σ : Matrix n n ℂ} (hσ : σ.IsHermitian) :
    dephaseIn hσ.eigenvectorUnitary σ = σ :=
  dephaseIn_of_conj_diagonal _ _ (spectral_decomp hσ)

/-- **Data processing for the measurement in the eigenbasis of `σ`**: for arbitrary faithful
states `ρ` and `σ`, measuring `ρ` in an eigenbasis of `σ` (a CPTP channel, see
`dephaseIn_isCPTP`) cannot increase the relative entropy with respect to `σ`. -/
