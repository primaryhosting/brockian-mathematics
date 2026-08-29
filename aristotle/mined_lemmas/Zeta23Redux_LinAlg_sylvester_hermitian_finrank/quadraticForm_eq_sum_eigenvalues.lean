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

/-- The positive index of inertia of a Hermitian matrix: the number of strictly positive
eigenvalues (counted with multiplicity, i.e. as a cardinality of the index set). -/

lemma quadraticForm_eq_sum_eigenvalues {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (x : Fin d → ℂ) :
    (star x ⬝ᵥ (A *ᵥ x)).re
      = ∑ i, hA.eigenvalues i *
          ‖((hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)ᴴ *ᵥ x) i‖ ^ 2 := by
  set U : Matrix (Fin d) (Fin d) ℂ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hU
  set c := Uᴴ *ᵥ x with hc
  have hAeq : A = U * (diagonal (RCLike.ofReal ∘ hA.eigenvalues)) * Uᴴ := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    rfl
  conv_lhs => rw [hAeq, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]
  have h1 : star x ᵥ* U = star c := by
    rw [hc, star_mulVec, conjTranspose_conjTranspose]
  rw [h1]
  have h2 : (diagonal (RCLike.ofReal ∘ hA.eigenvalues) : Matrix (Fin d) (Fin d) ℂ) *ᵥ c
      = fun i => (hA.eigenvalues i : ℂ) * c i := by
    funext i; simp [mulVec_diagonal]
  rw [h2]
  simp only [dotProduct, Pi.star_apply, RCLike.star_def]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_assoc, mul_comm (starRingEnd ℂ (c i)), mul_assoc, Complex.conj_mul']
  norm_cast

/-- **Sylvester's law of inertia** (Hermitian case, the direction used in the paper):
if the Hermitian form `x ↦ Re (star x ⬝ᵥ A *ᵥ x)` is positive definite on a complex subspace
`W ≤ (Fin d → ℂ)`, then `finrank W` is at most the number of strictly positive eigenvalues
of `A`. -/
