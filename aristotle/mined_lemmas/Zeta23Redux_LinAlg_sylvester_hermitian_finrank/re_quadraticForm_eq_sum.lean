/-
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

set_option grind.warning false

namespace Zeta23Redux.LinAlg

open Matrix

/-- The positive index of a Hermitian matrix: the number of its strictly positive
eigenvalues (counted with multiplicity, i.e. as a cardinality of indices). -/

lemma re_quadraticForm_eq_sum {d : ℕ} (U A : Matrix (Fin d) (Fin d) ℂ) (μ : Fin d → ℝ)
    (hspec : A = U * Matrix.diagonal (RCLike.ofReal ∘ μ) * Uᴴ) (x : Fin d → ℂ) :
    (star x ⬝ᵥ A *ᵥ x).re = ∑ i, μ i * Complex.normSq ((Uᴴ *ᵥ x) i) := by
  subst hspec
  have h1 : star x ⬝ᵥ (U * Matrix.diagonal (RCLike.ofReal ∘ μ) * Uᴴ) *ᵥ x
      = star (Uᴴ *ᵥ x) ⬝ᵥ (Matrix.diagonal (RCLike.ofReal ∘ μ) *ᵥ (Uᴴ *ᵥ x)) := by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  rw [h1]
  simp only [dotProduct, Matrix.mulVec_diagonal, Complex.re_sum, Pi.star_apply,
    RCLike.star_def, Function.comp_apply, Complex.normSq_apply, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, Complex.mul_im]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 : ((RCLike.ofReal (μ i) : ℂ)).re = μ i := rfl
  have h3 : ((RCLike.ofReal (μ i) : ℂ)).im = 0 := rfl
  rw [h2, h3]
  ring

/-- **Sylvester's law of inertia** (Hermitian case, the "pull-back does not increase the
positive index" direction).  If the Hermitian form `x ↦ Re (star x ⬝ᵥ A *ᵥ x)` associated to a
Hermitian complex matrix `A` is positive definite on a subspace `W`, then the dimension of `W`
is at most the number of strictly positive eigenvalues of `A`. -/
