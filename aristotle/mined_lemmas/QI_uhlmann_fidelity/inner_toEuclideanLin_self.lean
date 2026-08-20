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

theorem inner_toEuclideanLin_self {m : Type*} [Fintype m] [DecidableEq m] (A : Matrix n m ℂ)
    (x : EuclideanSpace ℂ m) :
    (inner ℂ (Matrix.toEuclideanLin A x) (Matrix.toEuclideanLin A x) : ℂ)
      = inner ℂ x (Matrix.toEuclideanLin (Aᴴ * A) x) := by
  have h : Matrix.toEuclideanLin (Aᴴ * A)
      = (LinearMap.adjoint (Matrix.toEuclideanLin A)).comp (Matrix.toEuclideanLin A) := by
    rw [Matrix.toLpLin_mul, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  rw [h]
  simp [LinearMap.adjoint_inner_right]

/-- Polar decomposition: every square complex matrix `M` factors as a unitary times the
positive semidefinite matrix `√(Mᴴ M)`. -/
