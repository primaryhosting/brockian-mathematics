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

/-- The Hermitian form attached to a matrix `A`: `x ↦ Re (star x ⬝ᵥ (A *ᵥ x))`. -/

noncomputable def posCoord (W : Submodule ℂ (Fin d → ℂ)) :
    W →ₗ[ℂ] ({i : Fin d // 0 < hA.eigenvalues i} → ℂ) where
  toFun x := fun i => diagCoord hA (x : Fin d → ℂ) i
  map_add' x y := by
    funext i
    simp [diagCoord, Matrix.mulVec_add]
  map_smul' c x := by
    funext i
    simp [diagCoord, Matrix.mulVec_smul]

end

/-- **Sylvester's law of inertia** (Hermitian form, the inequality used in the paper).
If the Hermitian form of a Hermitian matrix `A` is positive definite on a complex subspace `W`
of `Fin d → ℂ`, then `finrank W ≤ posIndex A`, the number of strictly positive eigenvalues
of `A`. -/
