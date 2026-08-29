import Mathlib

/-!
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped ComplexConjugate MatrixOrder ComplexOrder

namespace QI

/-! ### Basic definitions -/

section Defs

variable {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

/-- A density matrix (mixed state): a positive semidefinite matrix of unit trace. -/

noncomputable def lmap (M : Matrix K H ℂ) : EuclideanSpace ℂ H →ₗ[ℂ] EuclideanSpace ℂ K :=
  Matrix.toLpLin 2 2 M

omit [DecidableEq K] in
