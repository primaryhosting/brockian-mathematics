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

theorem cfc_conj_unitary (f : ℝ → ℝ) (u : unitary (Matrix n n ℂ)) {A : Matrix n n ℂ}
    (hA : IsSelfAdjoint A) :
    cfc f ((u : Matrix n n ℂ) * A * star (u : Matrix n n ℂ))
      = (u : Matrix n n ℂ) * cfc f A * star (u : Matrix n n ℂ) := by
  have h := StarAlgHomClass.map_cfc (Unitary.conjStarAlgAut ℝ (Matrix n n ℂ) u) f A
    (by rw [continuousOn_iff_continuous_restrict]; fun_prop)
    (by
      show Continuous fun X : Matrix n n ℂ =>
        (u : Matrix n n ℂ) * X * star (u : Matrix n n ℂ)
      fun_prop)
    hA (by simpa [Unitary.conjStarAlgAut_apply] using isSelfAdjoint_conj u hA)
  simp only [Unitary.conjStarAlgAut_apply] at h
  exact h.symm

/-- `Matrix.diagonal` as an `ℝ`-algebra homomorphism. -/
