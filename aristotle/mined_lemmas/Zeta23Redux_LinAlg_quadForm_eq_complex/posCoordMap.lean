import Mathlib
/-!
# Sylvester Hermitian Finrank
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.sylvester_hermitian_finrank
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

namespace Zeta23Redux.LinAlg

open Matrix

variable {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}

/-- The positive index of inertia of a Hermitian matrix: the number of strictly positive
eigenvalues (counted with multiplicity, i.e. over the index set of the matrix). -/

noncomputable def posCoordMap (hA : A.IsHermitian) :
    (Fin d → ℂ) →ₗ[ℂ] ({i : Fin d // 0 < hA.eigenvalues i} → ℂ) where
  toFun x i := eigCoord hA x i
  map_add' x y := by
    funext i
    simp [eigCoord, dotProduct_add]
  map_smul' c x := by
    funext i
    simp [eigCoord, dotProduct_smul]

/-- **Sylvester's law of inertia** (Hermitian version, the inequality direction used in the
paper): if the Hermitian form `x ↦ Re (star x ⬝ᵥ A *ᵥ x)` is positive definite on a subspace
`W`, then `finrank W ≤ posIndex A`. -/
