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

theorem trace_mul_posSemidef_nonneg {A B : Matrix n n ℂ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ (Matrix.trace (A * B)).re := by
  obtain ⟨C, hC⟩ := Matrix.posSemidef_iff_eq_conjTranspose_mul_self.mp hB
  have h1 : Matrix.trace (A * B) = Matrix.trace (C * A * Cᴴ) := by
    rw [hC, ← mul_assoc, Matrix.trace_mul_comm (A * Cᴴ) C, mul_assoc]
  have h3 := (hA.mul_mul_conjTranspose_same C).trace_nonneg
  rw [h1]
  simpa using (Complex.le_def.mp h3).1

/-! ### Kraus channels and their adjoints -/

/-- The channel attached to a Kraus family. -/
