/-
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Statement: Fidelity equals the maximal overlap over purifications (Uhlmann's theorem).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Statement: Fidelity equals the maximal overlap over purifications (Uhlmann's theorem).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped MatrixOrder ComplexOrder

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Basic notions

We work with a finite dimensional quantum system with Hilbert space `EuclideanSpace ℂ n`.
States are described by positive semidefinite matrices, and a purification of a state `ρ`
on the system is a vector of the composite system `EuclideanSpace ℂ (n × m)` (the tensor
product of the system with an ancilla) whose reduced density matrix (the partial trace over
the ancilla) is `ρ`.
-/

/-- The partial trace over the second (ancilla) tensor factor. -/

theorem exists_unitary_trace_mul_eq (M : Matrix n n ℂ) :
    ∃ U ∈ unitaryGroup n ℂ,
      Matrix.trace (M * U) = (Matrix.trace (CFC.sqrt (Mᴴ * M)) : ℂ) := by
  obtain ⟨W, hW, hM⟩ := exists_unitary_mul_sqrt M
  set P := CFC.sqrt (Mᴴ * M) with hPdef
  have hWstar : Wᴴ * W = 1 := Matrix.mem_unitaryGroup_iff'.mp hW
  refine ⟨Wᴴ, Unitary.star_mem hW, ?_⟩
  conv_lhs => rw [hM]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hWstar, Matrix.one_mul]

/-! ## Uhlmann's theorem, matrix form -/

/-- Uhlmann's theorem in matrix language: writing purifications of `ρ` as square matrices `A`
with `A Aᴴ = ρ`, the fidelity is the maximum of `|tr (Aᴴ B)|`. -/
