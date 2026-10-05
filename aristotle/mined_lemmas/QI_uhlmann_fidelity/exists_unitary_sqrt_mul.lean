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

theorem exists_unitary_sqrt_mul {ρ : Matrix n n ℂ} (A : Matrix n n ℂ) (hA : A * Aᴴ = ρ) :
    ∃ U : Matrix n n ℂ, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ A = CFC.sqrt ρ * U := by
  obtain ⟨U, hU1, hU2, hU3⟩ := exists_unitary_mul_sqrt Aᴴ
  rw [Matrix.conjTranspose_conjTranspose, hA] at hU3
  refine ⟨Uᴴ, by simpa using hU2, by simpa using hU1, ?_⟩
  have hsqrtH : (CFC.sqrt ρ)ᴴ = CFC.sqrt ρ := (CFC.sqrt_nonneg ρ).posSemidef.1
  have := congrArg Matrix.conjTranspose hU3
  rwa [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul, hsqrtH] at this

/-! ### The variational characterisation of the trace norm -/

omit [DecidableEq n] in
