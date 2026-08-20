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

theorem integral_chi_eq {P Q : Matrix n n ℂ} (hP : P.PosDef) (hQ : Q.PosDef) :
    (∫ t in Set.Ioi (0 : ℝ), chi t hP.1 hQ.1 / (1 + t) ^ 2)
      = ∑ j, ∑ k, Complex.normSq ((star (hP.1.eigenvectorUnitary : Matrix n n ℂ)
            * (hQ.1.eigenvectorUnitary : Matrix n n ℂ)) j k)
          * (hP.1.eigenvalues j * Real.log (hP.1.eigenvalues j)
              - hP.1.eigenvalues j * Real.log (hQ.1.eigenvalues k)
              - hP.1.eigenvalues j + hQ.1.eigenvalues k) := by
  simp_rw [fun t => chi_div_eq_sum t hP.1 hQ.1]
  rw [integral_finset_sum _ fun j _ =>
    integrable_finset_sum _ fun k _ =>
      (integrableOn_scalar_chi (hP.eigenvalues_pos j) (hQ.eigenvalues_pos k)).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finset_sum _ fun k _ =>
    (integrableOn_scalar_chi (hP.eigenvalues_pos j) (hQ.eigenvalues_pos k)).const_mul _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, integral_scalar_chi (hP.eigenvalues_pos j) (hQ.eigenvalues_pos k)]

/-- **Integral formula for the relative entropy.** -/
