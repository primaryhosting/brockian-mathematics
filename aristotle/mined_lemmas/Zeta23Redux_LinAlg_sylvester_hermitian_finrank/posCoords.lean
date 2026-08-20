/-
# Sylvester Hermitian Finrank
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.sylvester_hermitian_finrank
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- The positive index of inertia of a Hermitian matrix `A`: the number of indices `i` at which
the eigenvalue function `hA.eigenvalues` is strictly positive (i.e. the number of strictly
positive eigenvalues of `A`, counted with multiplicity). -/

noncomputable def posCoords (hA : A.IsHermitian) :
    (Fin d → ℂ) →ₗ[ℂ] ({i : Fin d // 0 < hA.eigenvalues i} → ℂ) where
  toFun x := fun i => inner ℂ (hA.eigenvectorBasis i) (WithLp.toLp 2 x)
  map_add' x y := by
    funext i
    simp
  map_smul' c x := by
    funext i
    simp

/-- **Sylvester's law of inertia** (Hermitian version, the inequality used in the paper):
if the Hermitian form `x ↦ Re (star x ⬝ᵥ A *ᵥ x)` attached to a Hermitian matrix `A` is positive
definite on a complex subspace `W` of `Fin d → ℂ`, then `finrank W` is at most the positive index
of inertia of `A` (the number of strictly positive eigenvalues of `A`). -/
