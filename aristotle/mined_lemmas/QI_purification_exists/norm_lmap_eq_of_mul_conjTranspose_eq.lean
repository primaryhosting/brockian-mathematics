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

lemma norm_lmap_eq_of_mul_conjTranspose_eq {A B : Matrix H K ℂ} (h : A * Aᴴ = B * Bᴴ)
    (x : EuclideanSpace ℂ H) : ‖lmap Aᴴ x‖ = ‖lmap Bᴴ x‖ := by
  have h1 : (inner ℂ (lmap Aᴴ x) (lmap Aᴴ x) : ℂ) = inner ℂ (lmap Bᴴ x) (lmap Bᴴ x) := by
    rw [inner_lmap_self, inner_lmap_self, h]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h1
  have h2 : ‖lmap Aᴴ x‖ ^ 2 = ‖lmap Bᴴ x‖ ^ 2 := by exact_mod_cast h1
  nlinarith [norm_nonneg (lmap Aᴴ x), norm_nonneg (lmap Bᴴ x)]

end Lin

/-! ### Extending a partial isometry -/

section Isom

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- Two linear maps into a finite-dimensional inner product space with the same pointwise
norms differ by a linear isometry of the target. -/
