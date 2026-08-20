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

lemma spectral_conjTranspose {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *
        Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) *
        (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)ᴴ := by
  have h := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  simpa [Matrix.star_eq_conjTranspose] using h

/-- Diagonalisation of the Hermitian quadratic form: if `A = U * diagonal μ * Uᴴ` then
`Re (star x ⬝ᵥ A *ᵥ x) = ∑ i, μ i * ‖(Uᴴ *ᵥ x) i‖²`. -/
