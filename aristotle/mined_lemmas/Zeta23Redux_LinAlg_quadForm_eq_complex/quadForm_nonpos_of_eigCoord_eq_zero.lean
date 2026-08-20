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

lemma quadForm_nonpos_of_eigCoord_eq_zero (hA : A.IsHermitian) (x : Fin d → ℂ)
    (hx : ∀ i, 0 < hA.eigenvalues i → eigCoord hA x i = 0) :
    (star x ⬝ᵥ A *ᵥ x).re ≤ 0 := by
  rw [quadForm_eq hA x]
  refine Finset.sum_nonpos fun i _ => ?_
  rcases lt_or_ge 0 (hA.eigenvalues i) with h | h
  · simp [hx i h]
  · exact mul_nonpos_of_nonpos_of_nonneg h (by positivity)

/-- The eigenvector coordinates along the positive eigenvalues, as a linear map. -/
