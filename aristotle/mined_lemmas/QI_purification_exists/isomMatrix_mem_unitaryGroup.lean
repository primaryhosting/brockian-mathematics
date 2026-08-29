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

lemma isomMatrix_mem_unitaryGroup (L : EuclideanSpace ℂ K →ₗᵢ[ℂ] EuclideanSpace ℂ K) :
    isomMatrix L ∈ Matrix.unitaryGroup K ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext k l
  have hinner := L.inner_map_map (EuclideanSpace.single k (1 : ℂ))
    (EuclideanSpace.single l (1 : ℂ))
  simp only [PiLp.inner_apply, RCLike.inner_apply] at hinner
  have hl : (star (isomMatrix L) * isomMatrix L) k l
      = ∑ i, conj (isomMatrix L i k) * isomMatrix L i l := by
    simp [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
  rw [hl]
  have : ∑ i, conj (isomMatrix L i k) * isomMatrix L i l
      = ∑ i, (L (EuclideanSpace.single l (1 : ℂ))) i *
          conj ((L (EuclideanSpace.single k (1 : ℂ))) i) := by
    exact Finset.sum_congr rfl fun i _ => by simp [isomMatrix, mul_comm]
  rw [this, hinner]
  simp [EuclideanSpace.single_apply, Matrix.one_apply, eq_comm]

omit [Fintype K] [DecidableEq K] in
