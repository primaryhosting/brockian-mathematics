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
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Redux.LinAlg

open Matrix

/-- The positive index of a Hermitian matrix: the number of its strictly positive eigenvalues
(counted with multiplicity, i.e. as a number of indices).  For matrices that are not Hermitian
the value is set to `0`. -/

lemma quadratic_form_eq_sum {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian)
    (x : Fin d → ℂ) :
    (star x ⬝ᵥ (A *ᵥ x)).re =
      ∑ i, hA.eigenvalues i *
        Complex.normSq (((star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)) *ᵥ x) i) := by
  set U : Matrix (Fin d) (Fin d) ℂ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hU
  set lam : Fin d → ℝ := hA.eigenvalues with hlam
  set y : Fin d → ℂ := star U *ᵥ x with hy
  have hAeq : A = U * (diagonal (RCLike.ofReal ∘ lam)) * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
  have h1 : A *ᵥ x = U *ᵥ ((diagonal (RCLike.ofReal ∘ lam)) *ᵥ y) := by
    rw [hAeq, hy, ← mulVec_mulVec, ← mulVec_mulVec]
  have h2 : star x ᵥ* U = star y := by
    rw [hy, star_mulVec, ← Matrix.star_eq_conjTranspose, star_star]
  rw [h1, dotProduct_mulVec, h2, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mulVec_diagonal, Complex.normSq_apply]
  ring

/-- **Sylvester's law of inertia** (Hermitian case, the direction used in the paper):
if the Hermitian form associated with a Hermitian matrix `A` is positive definite on a complex
subspace `W` of `Fin d → ℂ`, then `finrank W` is at most the number of strictly positive
eigenvalues of `A`.  In other words, pulling back does not increase the positive index. -/
