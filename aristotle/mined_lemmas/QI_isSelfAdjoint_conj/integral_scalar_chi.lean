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

theorem integral_scalar_chi {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ∫ t in Set.Ioi (0 : ℝ), (p - q) ^ 2 / ((t * p + q) * (1 + t) ^ 2)
      = p * Real.log p - p * Real.log q - p + q := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg (continuousWithinAt_scalarPrim hq)
    (fun x hx => hasDerivAt_scalarPrim hq hx hp)
    (fun x hx => scalar_integrand_nonneg hp hq hx) (tendsto_scalarPrim hp hq)]
  simp [scalarPrim]
  ring

