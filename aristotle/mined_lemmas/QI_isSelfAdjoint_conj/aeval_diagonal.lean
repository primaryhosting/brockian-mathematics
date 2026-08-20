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

theorem aeval_diagonal (p : Polynomial ℝ) (d : n → ℝ) :
    (Polynomial.aeval (Matrix.diagonal (fun i => (d i : ℂ)))) p
      = Matrix.diagonal (fun i => ((p.eval (d i) : ℝ) : ℂ)) := by
  have h : Matrix.diagonal (fun i => (d i : ℂ)) = diagAlgHom n (fun i => (d i : ℂ)) := rfl
  rw [h, Polynomial.aeval_algHom_apply]
  show Matrix.diagonal _ = _
  congr 1
  funext i
  have h1 := Polynomial.aeval_algHom_apply (Pi.evalAlgHom ℝ (fun _ : n => ℂ) i)
    (fun i => (d i : ℂ)) p
  simp only [Pi.evalAlgHom_apply] at h1
  rw [← h1]
  simpa using (Polynomial.aeval_algebraMap_apply ℂ (d i) p)

omit [Fintype n] in
