/-!
# Sylvester Hermitian Finrank
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.sylvester_hermitian_finrank
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

open Matrix

namespace Zeta23Redux.LinAlg

variable {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}

/-- The positive index of inertia of a Hermitian matrix: the number of strictly positive
eigenvalues (counted with multiplicity, i.e. as a cardinality of an index subtype). -/

lemma quad_eq (hA : A.IsHermitian) (x : Fin d → ℂ) :
    (star x ⬝ᵥ A *ᵥ x).re
      = ∑ i, hA.eigenvalues i *
          ‖(star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *ᵥ x) i‖ ^ 2 := by
  set U : Matrix (Fin d) (Fin d) ℂ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hU
  set y := star U *ᵥ x with hy
  have hAx : A *ᵥ x
      = U *ᵥ ((diagonal (RCLike.ofReal ∘ hA.eigenvalues) : Matrix (Fin d) (Fin d) ℂ) *ᵥ y) := by
    conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rw [hy, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hstar : star x ᵥ* U = star y := by
    rw [hy, Matrix.star_mulVec]
    simp [hU, Matrix.star_eq_conjTranspose]
  rw [hAx, Matrix.dotProduct_mulVec, hstar]
  have hsum : (star y ⬝ᵥ (diagonal (RCLike.ofReal ∘ hA.eigenvalues) : Matrix (Fin d) (Fin d) ℂ) *ᵥ y)
      = ∑ i, (starRingEnd ℂ) (y i) * ((hA.eigenvalues i : ℂ) * y i) := by
    simp [dotProduct, Matrix.mulVec_diagonal]
  rw [hsum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.mul_re, Complex.normSq_apply]
  ring

/-- **Sylvester's law of inertia** (Hermitian case, the direction used in the paper):
if the Hermitian form `x ↦ Re (star x ⬝ᵥ A *ᵥ x)` attached to a Hermitian matrix `A` is
positive definite on a complex subspace `W ≤ (Fin d → ℂ)`, then
`finrank W ≤ posIndex A`, the number of strictly positive eigenvalues of `A`. -/
