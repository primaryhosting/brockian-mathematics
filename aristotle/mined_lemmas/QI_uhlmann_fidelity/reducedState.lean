import Mathlib

/-!
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Finset
open scoped MatrixOrder ComplexOrder

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The dictionary between vectors of `H ⊗ H` and matrices

We model the Hilbert space `H` of a finite quantum system by `EuclideanSpace ℂ n` and the
composite system `H ⊗ H` by `EuclideanSpace ℂ (n × n)`.  A vector of the composite system is
the same thing as a matrix of coefficients. -/

/-- The matrix of coefficients of a vector of `H ⊗ H = EuclideanSpace ℂ (n × n)`. -/

noncomputable def reducedState (ψ : EuclideanSpace ℂ (n × n)) : Matrix n n ℂ :=
  .of fun i i' => ∑ j, ψ (i, j) * (starRingEnd ℂ) (ψ (i', j))

/-- The trace norm `‖M‖₁ = Tr √(Mᴴ M)`. -/
