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

theorem isDensity_dephase {ρ : Matrix n n ℂ} (hρ : IsDensity ρ) : IsDensity (dephase ρ) := by
  obtain ⟨hpd, htr⟩ := hρ
  constructor
  · have : dephase ρ = Matrix.diagonal (fun i => (((ρ i i).re : ℝ) : ℂ)) := by
      rw [dephase]
      congr 1
      funext i
      exact (posDef_diag_re hpd i).2
    rw [this]
    refine Matrix.PosDef.diagonal fun i => ?_
    rw [Complex.lt_def]
    simpa using (posDef_diag_re hpd i).1
  · rw [dephase, Matrix.trace_diagonal, ← htr, Matrix.trace]
    rfl

/-- **Data processing for the dephasing channel**: for an arbitrary faithful state `ρ` and a
faithful state `σ` which is diagonal in the measurement basis, the relative entropy does not
increase under the (CPTP) completely dephasing channel. -/
