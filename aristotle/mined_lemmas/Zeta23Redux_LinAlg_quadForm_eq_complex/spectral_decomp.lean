import Mathlib

/-!
# Quad Form Eq Complex
Category: Linalg
Target: Zeta23Redux.LinAlg.quadForm_eq_complex
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

namespace Zeta23Redux.LinAlg

open Matrix

/-- The coordinates of a vector `x` in the eigenbasis of a Hermitian matrix `A`, i.e.
`x` expressed via the unitary matrix of eigenvectors of `A`. -/

theorem spectral_decomp {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix n n ℂ) * diagonal (RCLike.ofReal ∘ hA.eigenvalues) *
      star (hA.eigenvectorUnitary : Matrix n n ℂ) := by
  have h := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  exact h

/-- Hermitian quadratic form in eigencoordinates: for a Hermitian matrix `A` and a vector `x`,
`star x ⬝ᵥ A *ᵥ x = ∑ i, λ i * ‖(eigencoord x) i‖ ^ 2`, as an equality of complex numbers. -/
