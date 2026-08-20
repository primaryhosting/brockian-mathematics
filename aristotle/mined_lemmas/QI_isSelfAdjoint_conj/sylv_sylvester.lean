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

theorem sylv_sylvester {t : ℝ} (ht : 0 < t) {P Q : Matrix n n ℂ} (hP : P.PosDef)
    (hQ : Q.PosDef) :
    (t : ℂ) • (P * sylv t hP.1 hQ.1) + sylv t hP.1 hQ.1 * Q = P - Q :=
  sylvAux_sylvester ht (Unitary.coe_star_mul_self _) (Unitary.coe_mul_star_self _)
    (Unitary.coe_star_mul_self _) (Unitary.coe_mul_star_self _) hP.eigenvalues_pos
    hQ.eigenvalues_pos (spectral_decomp hP.1) (spectral_decomp hQ.1)

/-- The spectral expression of `χ_t`. -/
