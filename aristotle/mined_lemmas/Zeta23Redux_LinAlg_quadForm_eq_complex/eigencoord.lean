/-
# Quad Form Eq Complex
Category: Linalg
Target: Zeta23Redux.LinAlg.quadForm_eq_complex
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Quad Form Eq Complex
Category: Linalg
Target: Zeta23Redux.LinAlg.quadForm_eq_complex
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix

namespace Zeta23Redux.LinAlg

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}

/-- The coordinates of a vector `x` in the orthonormal eigenbasis of a Hermitian matrix `A`,
obtained by applying the adjoint of the eigenvector unitary of `A` to `x`. -/

noncomputable def eigenCoord (hA : A.IsHermitian) (x : n → ℂ) : n → ℂ :=
  star (hA.eigenvectorUnitary : Matrix n n ℂ) *ᵥ x

/-- **Hermitian quadratic form in eigencoordinates**: for a Hermitian complex matrix `A`,
the quadratic form `star x ⬝ᵥ A *ᵥ x` equals `∑ i, λ i * ‖(eigenCoord x) i‖ ^ 2`,
where the `λ i` are the eigenvalues of `A` (viewed as complex numbers). -/
