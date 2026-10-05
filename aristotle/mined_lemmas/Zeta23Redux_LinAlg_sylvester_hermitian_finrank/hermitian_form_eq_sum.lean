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

variable {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}

/-- The (finite) set of indices at which a Hermitian matrix has a strictly positive
eigenvalue. -/

theorem hermitian_form_eq_sum (hA : A.IsHermitian) (x : Fin d → ℂ) :
    (star x ⬝ᵥ (A *ᵥ x)).re =
      ∑ i, hA.eigenvalues i *
        ‖(star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *ᵥ x) i‖ ^ 2 := by
  set U : Matrix (Fin d) (Fin d) ℂ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hU
  set y := star U *ᵥ x with hy
  have key : star x ⬝ᵥ (A *ᵥ x) = ∑ i, ((hA.eigenvalues i : ℂ) * ((‖y i‖ ^ 2 : ℝ) : ℂ)) := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]
    have h1 : star x ᵥ* U = star y := by
      rw [hy, star_mulVec]
      simp [Matrix.star_eq_conjTranspose]
    rw [h1, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hy]
    have h2 : star (y i) * y i = ((‖y i‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_mul']
      norm_cast
    simp only [Matrix.mulVec_diagonal, Function.comp_apply, Complex.coe_algebraMap]
    rw [show star y i * ((hA.eigenvalues i : ℂ) * y i)
        = (hA.eigenvalues i : ℂ) * (star (y i) * y i) by simp [Pi.star_apply]; ring, h2]
  rw [key]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.ofReal_mul, Complex.ofReal_re]

/-- **Sylvester's law of inertia** (Hermitian version, the direction used in the paper).
If the Hermitian form `x ↦ Re (star x ⬝ᵥ A *ᵥ x)` of a Hermitian matrix `A` is positive
definite on a complex subspace `W ≤ (Fin d → ℂ)`, then `finrank W ≤ posIndex A`, the number
of strictly positive eigenvalues of `A`. -/
