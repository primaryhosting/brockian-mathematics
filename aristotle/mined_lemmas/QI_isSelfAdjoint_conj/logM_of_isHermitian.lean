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

theorem logM_of_isHermitian {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    logM A = (hA.eigenvectorUnitary : Matrix n n ℂ)
      * Matrix.diagonal (fun i => ((Real.log (hA.eigenvalues i) : ℝ) : ℂ))
      * star (hA.eigenvectorUnitary : Matrix n n ℂ) := by
  conv_lhs => rw [spectral_decomp hA]
  exact logM_conj_diagonal _ _

/-- The "cross term" `Tr(ρ log σ)` expressed through the eigenvalues of `ρ` and `σ` and the
doubly stochastic matrix relating their eigenbases. -/
