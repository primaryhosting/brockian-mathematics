/-
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Zeta23Redux.LinAlg

open Matrix

variable {d : ℕ}

/-- The number of strictly positive eigenvalues of a Hermitian matrix. -/

lemma qform_nonpos_of_coeffs {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    {x : EuclideanSpace ℂ (Fin d)}
    (hx : ∀ i, 0 < hA.eigenvalues i → inner ℂ (hA.eigenvectorBasis i) x = 0) :
    qform A x ≤ 0 := by
  rw [qform_eq hA]
  refine Finset.sum_nonpos fun i _ => ?_
  rcases lt_or_ge 0 (hA.eigenvalues i) with hpos | hle
  · simp [hx i hpos]
  · exact mul_nonpos_of_nonpos_of_nonneg hle (sq_nonneg _)

/-- **Weyl monotonicity**: if every eigenvalue of the Hermitian perturbation `E` has absolute
value at most `θ`, then the number of eigenvalues of `A + E` strictly above `θ` is at most the
number of strictly positive eigenvalues of `A`. -/
