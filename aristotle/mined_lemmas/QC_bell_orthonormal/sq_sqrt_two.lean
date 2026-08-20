import Mathlib

/-!
# Bell Orthonormal
Category: Quantum Computing
Target: QC.bell_orthonormal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open scoped ComplexConjugate

/-- The two-qubit state space `ℂ² ⊗ ℂ²`, realised concretely as the Hilbert space
of functions `Fin 2 × Fin 2 → ℂ` with the standard inner product. -/
abbrev TwoQubit := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- Unnormalised coefficients of the four Bell states in the computational basis
`|00⟩, |01⟩, |10⟩, |11⟩`. -/

private lemma sq_sqrt_two : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
  have : (Real.sqrt 2 : ℝ) * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) this

/-- The Bell states are pairwise orthogonal unit vectors. -/
