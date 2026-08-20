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

theorem chi_div_eq_sum (t : ℝ) {P Q : Matrix n n ℂ} (hP : P.IsHermitian) (hQ : Q.IsHermitian) :
    chi t hP hQ / (1 + t) ^ 2
      = ∑ j, ∑ k, Complex.normSq ((star (hP.eigenvectorUnitary : Matrix n n ℂ)
            * (hQ.eigenvectorUnitary : Matrix n n ℂ)) j k)
          * ((hP.eigenvalues j - hQ.eigenvalues k) ^ 2
              / ((t * hP.eigenvalues j + hQ.eigenvalues k) * (1 + t) ^ 2)) := by
  rw [chi_eq_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [div_eq_mul_inv, mul_inv]
  ring

