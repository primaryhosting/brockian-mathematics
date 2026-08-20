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

private theorem scalar_integrand_nonneg {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {t : ℝ}
    (ht : 0 < t) : 0 ≤ (p - q) ^ 2 / ((t * p + q) * (1 + t) ^ 2) := by
  have hd1 : (0 : ℝ) < t * p + q := by nlinarith
  have hd2 : (0 : ℝ) < 1 + t := by linarith
  positivity

