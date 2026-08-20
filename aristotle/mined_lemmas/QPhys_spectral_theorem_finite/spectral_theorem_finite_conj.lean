/-
# Spectral Theorem Finite
Category: Quantum Physics
Target: QPhys.spectral_theorem_finite
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Spectral Theorem Finite
Category: Quantum Physics
Target: QPhys.spectral_theorem_finite
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QPhys

/-- **Spectral theorem (finite dimensions).**
Every Hermitian matrix `A` over `ℂ` is unitarily diagonalizable with real eigenvalues:
there are a unitary matrix `U` and a real-valued function `d` such that
`A = U * diagonal d * Uᴴ`, and each `d i` is genuinely an eigenvalue of `A`
(witnessed by a nonzero eigenvector). -/

theorem spectral_theorem_finite_conj {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    ∃ (U : Matrix n n ℂ) (d : n → ℝ),
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      Uᴴ * A * U = Matrix.diagonal (fun i => ((d i : ℂ))) := by
  obtain ⟨U, d, h1, h2, h3, -⟩ := spectral_theorem_finite hA
  refine ⟨U, d, h1, h2, ?_⟩
  rw [h3]
  rw [show Uᴴ * (U * Matrix.diagonal (fun i => ((d i : ℂ))) * Uᴴ) * U
      = (Uᴴ * U) * Matrix.diagonal (fun i => ((d i : ℂ))) * (Uᴴ * U) by
    simp [Matrix.mul_assoc]]
  simp [h1]

end QPhys

