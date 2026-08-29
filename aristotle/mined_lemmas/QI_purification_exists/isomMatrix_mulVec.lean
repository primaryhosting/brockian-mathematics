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

lemma isomMatrix_mulVec (L : EuclideanSpace ℂ K →ₗᵢ[ℂ] EuclideanSpace ℂ K)
    (v : EuclideanSpace ℂ K) (i : K) : (L v) i = ∑ j, isomMatrix L i j * v j := by
  have hv : v = ∑ j, v j • (EuclideanSpace.single j (1 : ℂ)) := by
    ext k; simp [Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum]
  simp [isomMatrix, mul_comm]

