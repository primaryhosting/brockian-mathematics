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

lemma posIndex_eq {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) :
    posIndex A = Fintype.card {i : Fin d // 0 < hA.eigenvalues i} := dif_pos hA

section

variable {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)

/-- The unitary change of coordinates diagonalizing `A`. -/
