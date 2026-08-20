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

theorem spectrum_diagonal_subset (d : n → ℝ) :
    spectrum ℝ (Matrix.diagonal (fun i => (d i : ℂ))) ⊆ Set.range d := by
  intro r hr
  by_contra hcon
  apply hr
  have h1 : algebraMap ℝ (Matrix n n ℂ) r - Matrix.diagonal (fun i => (d i : ℂ))
      = Matrix.diagonal (fun i => ((r : ℂ) - d i)) := by
    rw [Algebra.algebraMap_eq_smul_one]
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.diagonal]
  rw [resolventSet, Set.mem_setOf_eq, h1, Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal]
  refine isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => ?_)
  simp only [sub_ne_zero]
  intro h
  exact hcon ⟨i, by exact_mod_cast h.symm⟩

