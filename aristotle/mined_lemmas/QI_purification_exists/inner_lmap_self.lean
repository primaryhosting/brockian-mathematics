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

lemma inner_lmap_self (A : Matrix H K ℂ) (x : EuclideanSpace ℂ H) :
    (inner ℂ (lmap Aᴴ x) (lmap Aᴴ x) : ℂ) = ∑ i, ∑ j, conj (x i) * x j * (A * Aᴴ) i j := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, lmap, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Matrix.mul_apply, map_sum,
    map_mul, Finset.mul_sum, Finset.sum_mul, RCLike.star_def, starRingEnd_self_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => by ring

omit [DecidableEq K] in
