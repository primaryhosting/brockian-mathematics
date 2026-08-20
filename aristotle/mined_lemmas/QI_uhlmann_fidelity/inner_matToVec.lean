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

theorem inner_matToVec {m : Type*} [Fintype m] (A B : Matrix n m ℂ) :
    (inner ℂ (matToVec A) (matToVec B) : ℂ) = Matrix.trace (Aᴴ * B) := by
  rw [PiLp.inner_apply]
  simp only [matToVec, WithLp.ofLp_toLp, RCLike.inner_apply, Matrix.trace, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.diag_apply, ← Finset.sum_product']
  exact Fintype.sum_equiv (Equiv.prodComm n m) _ _ (fun p => by simp [mul_comm])

omit [DecidableEq n] in
