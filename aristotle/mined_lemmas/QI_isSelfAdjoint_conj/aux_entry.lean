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

private theorem aux_entry (r d : ℝ) (z : ℂ) :
    star ((r : ℂ) * z) * ((r : ℂ) * z / (d : ℂ)) = (((r ^ 2 / d) * Complex.normSq z : ℝ) : ℂ) := by
  have h1 : star ((r : ℂ) * z) = (r : ℂ) * star z := by rw [star_mul']; simp
  have h2 : star z * z = ((Complex.normSq z : ℝ) : ℂ) := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  rw [h1]
  push_cast
  rw [div_mul_eq_mul_div, ← h2]
  ring

