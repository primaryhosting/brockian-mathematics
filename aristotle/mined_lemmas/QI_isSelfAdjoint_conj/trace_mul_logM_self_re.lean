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

theorem trace_mul_logM_self_re {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) :
    (Matrix.trace (ρ * logM ρ)).re
      = ∑ i, hρ.eigenvalues i * Real.log (hρ.eigenvalues i) := by
  rw [trace_mul_logM_re hρ hρ]
  rw [Unitary.coe_star_mul_self]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-! ### Klein's inequality -/

/-- **Klein's inequality**: the quantum relative entropy of two faithful states is nonnegative. -/
