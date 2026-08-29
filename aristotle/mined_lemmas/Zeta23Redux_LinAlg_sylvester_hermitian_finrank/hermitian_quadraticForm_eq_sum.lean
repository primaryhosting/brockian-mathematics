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

open Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Zeta23Redux.LinAlg

/-- The positive index of inertia of a Hermitian matrix `A`: the number of indices `i` at which
the eigenvalue `hA.eigenvalues i` is strictly positive (i.e. the number of strictly positive
eigenvalues of `A`, counted with multiplicity). -/

theorem hermitian_quadraticForm_eq_sum {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (x : Fin d → ℂ) :
    (star x ⬝ᵥ (A *ᵥ x)).re
      = ∑ i, hA.eigenvalues i *
          Complex.normSq (((star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)) *ᵥ x) i) := by
  obtain ⟨U, hU⟩ : ∃ U : Matrix (Fin d) (Fin d) ℂ,
      U = (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) := ⟨_, rfl⟩
  obtain ⟨lam, hlam⟩ : ∃ lam : Fin d → ℝ, lam = hA.eigenvalues := ⟨_, rfl⟩
  rw [← hU, ← hlam]
  have hAeq : A = U * (Matrix.diagonal (RCLike.ofReal ∘ lam)) * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, hU, hlam]
  obtain ⟨y, hy⟩ : ∃ y : Fin d → ℂ, y = star U *ᵥ x := ⟨_, rfl⟩
  rw [← hy]
  have hstar : star x ᵥ* U = star y := by
    rw [hy, Matrix.star_mulVec, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  have key : star x ⬝ᵥ (A *ᵥ x)
      = star y ⬝ᵥ (Matrix.diagonal (RCLike.ofReal ∘ lam) *ᵥ y) := by
    rw [hAeq, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hstar, ← hy]
  rw [key]
  simp only [dotProduct, Matrix.mulVec_diagonal, Function.comp_apply,
    Pi.star_apply, RCLike.star_def, Complex.re_sum, Complex.normSq_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.mul_re, Complex.ofReal_re]
  ring

/-- If all the coordinates of `x` along eigenvectors with a strictly positive eigenvalue vanish,
then the Hermitian form of `A` at `x` is nonpositive. -/
