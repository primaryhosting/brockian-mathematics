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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Zeta23Redux.LinAlg

open Matrix

/-- The positive index of a Hermitian matrix: the number of strictly positive eigenvalues
(counted with multiplicity, i.e. the number of indices carrying a positive eigenvalue). -/

theorem re_quadratic_form_of_spectral {d : ℕ} (A U : Matrix (Fin d) (Fin d) ℂ) (L : Fin d → ℝ)
    (hspec : A = U * diagonal (RCLike.ofReal ∘ L) * star U) (x : Fin d → ℂ) :
    (star x ⬝ᵥ A *ᵥ x).re = ∑ i, L i * ‖(star U *ᵥ x) i‖ ^ 2 := by
  set y : Fin d → ℂ := star U *ᵥ x with hy
  have key : star x ⬝ᵥ A *ᵥ x = star y ⬝ᵥ (diagonal (RCLike.ofReal ∘ L) *ᵥ y) := by
    rw [hspec, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec]
    congr 1
    rw [hy, Matrix.star_mulVec, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
  rw [key]
  simp only [dotProduct, mulVec_diagonal, Complex.re_sum, Function.comp_apply,
    Pi.star_apply, RCLike.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.mul_im]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Complex.norm_eq_sqrt_sq_add_sq, Real.sq_sqrt (by positivity)]
  norm_num
  ring

/-- **Sylvester's law of inertia** (Hermitian case, the "pull-back does not increase the
positive index" direction).  If `A` is a Hermitian complex `d × d` matrix and `W` is a
complex subspace of `Fin d → ℂ` on which the Hermitian form `x ↦ Re (star x ⬝ᵥ A *ᵥ x)` is
positive definite, then `finrank W ≤ posIndex A`, the number of strictly positive
eigenvalues of `A`. -/
