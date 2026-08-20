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

theorem cfc_diagonal (f : ℝ → ℝ) (d : n → ℝ) :
    cfc f (Matrix.diagonal (fun i => (d i : ℂ)))
      = Matrix.diagonal (fun i => ((f (d i) : ℝ) : ℂ)) := by
  classical
  set S : Finset ℝ := Finset.image d Finset.univ with hS
  set p : Polynomial ℝ := Lagrange.interpolate S id f with hp
  have hnode : ∀ x ∈ S, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) f
      (Set.injOn_of_injective Function.injective_id) hx
  have heq : Set.EqOn f (fun x => p.eval x)
      (spectrum ℝ (Matrix.diagonal (fun i => (d i : ℂ)))) := by
    intro x hx
    obtain ⟨i, rfl⟩ := spectrum_diagonal_subset d hx
    exact (hnode _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)).symm
  rw [cfc_congr heq, cfc_polynomial p _ (isSelfAdjoint_diagonal d), aeval_diagonal]
  congr 1
  funext i
  rw [hnode _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)]

/-- The workhorse: the matrix logarithm of `U D U*` with `D` diagonal real. -/
