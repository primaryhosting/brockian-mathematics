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

lemma lmap_apply (M : Matrix K H ℂ) (x : EuclideanSpace ℂ H) (k : K) :
    (lmap M x) k = ∑ i, M k i * x i := by
  simp [lmap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]

omit [DecidableEq K] in
