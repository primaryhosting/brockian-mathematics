import Mathlib

/-!
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open scoped ComplexOrder
open scoped MatrixOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Extending a partial isometry -/

/-- If `‖p x‖ = ‖m x‖` for all `x`, then the assignment `p x ↦ m x` extends to a global
linear isometry `w` of the (finite dimensional) space, i.e. `w (p x) = m x` for all `x`. -/

lemma exists_unitary_polar_left (M : Matrix n n ℂ) :
    ∃ U : Matrix n n ℂ, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ M = CFC.sqrt (M * Mᴴ) * U := by
  obtain ⟨U, h1, h2, h3⟩ := exists_unitary_polar Mᴴ
  rw [Matrix.conjTranspose_conjTranspose] at h3
  refine ⟨Uᴴ, by simpa using h2, by simpa using h1, ?_⟩
  have h4 := congrArg Matrix.conjTranspose h3
  rw [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul,
    ((CFC.sqrt_nonneg (M * Mᴴ)).posSemidef :
      (CFC.sqrt (M * Mᴴ) : Matrix n n ℂ).PosSemidef).isHermitian.eq] at h4
  exact h4

/-- Every matrix `A` with `A Aᴴ = ρ` is of the form `√ρ * U` with `U` unitary; conversely all
such matrices satisfy `A Aᴴ = ρ` when `ρ` is positive semidefinite. -/
