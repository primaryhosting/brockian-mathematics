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
theorem spectral_theorem_finite {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    ∃ (U : Matrix n n ℂ) (d : n → ℝ),
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      A = U * Matrix.diagonal (fun i => ((d i : ℂ))) * Uᴴ ∧
      ∀ i, ∃ v : n → ℂ, v ≠ 0 ∧ A *ᵥ v = ((d i : ℂ)) • v := by
  refine ⟨(hA.eigenvectorUnitary : Matrix n n ℂ), hA.eigenvalues, ?_, ?_, ?_, ?_⟩
  · exact hA.eigenvectorUnitary.2.1
  · exact hA.eigenvectorUnitary.2.2
  · have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa [Function.comp] using h
  · intro i
    refine ⟨⇑(hA.eigenvectorBasis i), ?_, ?_⟩
    · intro hv
      have h1 : ‖hA.eigenvectorBasis i‖ = 1 := hA.eigenvectorBasis.norm_eq_one i
      have h2 : (hA.eigenvectorBasis i) = 0 := by
        ext j
        exact congrFun hv j
      rw [h2] at h1
      simp at h1
    · have := hA.mulVec_eigenvectorBasis i
      rw [this]
      ext j
      simp [Complex.real_smul]

/-- Companion form of the finite-dimensional spectral theorem: a Hermitian matrix is brought to
real diagonal form by conjugation with a unitary, `Uᴴ * A * U = diagonal d`. -/
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

