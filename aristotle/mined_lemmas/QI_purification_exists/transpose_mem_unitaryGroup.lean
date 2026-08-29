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

lemma transpose_mem_unitaryGroup {U : Matrix K K ℂ} (h : U ∈ Matrix.unitaryGroup K ℂ) :
    Uᵀ ∈ Matrix.unitaryGroup K ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] at h
  rw [Matrix.mem_unitaryGroup_iff]
  have h2 := congrArg Matrix.transpose h
  rw [Matrix.transpose_mul, Matrix.transpose_one, star_eq_star_transpose] at h2
  exact h2

/-- **Unitary freedom**: if `A Aᴴ = B Bᴴ` then `B = A Uᵀ` for some unitary `U`. -/
