import Mathlib

/-!
# Sylvester Finrank Le Pos Index
Category: Brockian Corpus
Target: Zeta23Core.sylvester_finrank_le_posIndex
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Zeta23Core

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜}

/-- The positive index (number of positive eigenvalues, with multiplicity) of a Hermitian
matrix. -/

theorem isHermitian_eq_unitary_mul_diagonal_mul_star (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix n n 𝕜) *
      diagonal (fun i => ((hA.eigenvalues i : ℝ) : 𝕜)) *
      star (hA.eigenvectorUnitary : Matrix n n 𝕜) := by
  conv_lhs => rw [hA.spectral_theorem]
  simp [Unitary.conjStarAlgAut_apply, Function.comp_def]

/-- Diagonalizing the quadratic form: if `A = U * diagonal d * Uᴴ`, then
`Re (xᴴ A x) = ∑ i, d i * ‖(Uᴴ x) i‖ ^ 2`. -/
