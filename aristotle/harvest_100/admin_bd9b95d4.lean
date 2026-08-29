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

import Mathlib
/-!
# Spectral Theorem Finite
Category: Quantum Physics
Target: QPhys.spectral_theorem_finite
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

open Matrix

/-- **Spectral theorem for Hermitian matrices.** Every Hermitian matrix `A` over `ℂ`
(indexed by a finite type) is unitarily diagonalizable with real eigenvalues: there is a
unitary matrix `U` and a real-valued function `d` of eigenvalues with
`A = U * diagonal d * Uᴴ`, where each `d i` lies in the real spectrum of `A` and the
`i`-th column of `U` is a corresponding eigenvector.

The key input is Mathlib's `Matrix.IsHermitian.spectral_theorem`. -/
theorem spectral_theorem_finite {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    ∃ (U : Matrix n n ℂ) (d : n → ℝ),
      U ∈ Matrix.unitaryGroup n ℂ ∧
      A = U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ ∧
      (∀ i, d i ∈ spectrum ℝ A) ∧
      (∀ i, A *ᵥ (fun j => U j i) = (d i : ℂ) • (fun j => U j i)) := by
  refine ⟨(hA.eigenvectorUnitary : Matrix n n ℂ), hA.eigenvalues,
    (hA.eigenvectorUnitary).2, ?_, fun i => hA.eigenvalues_mem_spectrum_real i, fun i => ?_⟩
  · conv_lhs => rw [hA.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.star_eq_conjTranspose]
  · have h := hA.mulVec_eigenvectorBasis i
    have hcol : (fun j => (hA.eigenvectorUnitary : Matrix n n ℂ) j i)
        = ⇑(hA.eigenvectorBasis i) := rfl
    rw [hcol, h]
    funext j
    simp [Complex.real_smul]

end QPhys

