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

lemma quadForm_eq (hA : A.IsHermitian) (x : Fin d → ℂ) :
    (star x ⬝ᵥ A *ᵥ x).re = ∑ i, hA.eigenvalues i * ‖eigCoord hA x i‖ ^ 2 := by
  rw [quadForm_eq_complex hA x, Complex.ofReal_re]

/-- If all the coordinates of `x` along positive eigenvectors vanish, then the quadratic form
is nonpositive at `x`. -/
