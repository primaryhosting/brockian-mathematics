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

theorem integrableOn_chi {P Q : Matrix n n ℂ} (hP : P.PosDef) (hQ : Q.PosDef) :
    IntegrableOn (fun t : ℝ => chi t hP.1 hQ.1 / (1 + t) ^ 2) (Set.Ioi (0 : ℝ)) := by
  simp_rw [fun t => chi_div_eq_sum t hP.1 hQ.1]
  refine integrable_finset_sum _ fun j _ => integrable_finset_sum _ fun k _ => ?_
  exact (integrableOn_scalar_chi (hP.eigenvalues_pos j) (hQ.eigenvalues_pos k)).const_mul _

