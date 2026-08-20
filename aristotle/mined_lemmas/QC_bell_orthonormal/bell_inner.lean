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

theorem bell_inner (k l : Fin 4) :
    (inner ℂ (bell k) (bell l) : ℂ) = if k = l then 1 else 0 := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, RCLike.inner_apply, bell_apply, map_mul, map_inv₀,
    Complex.conj_ofReal]
  set c : ℂ := (Real.sqrt 2 : ℂ)⁻¹ with hc
  have hcc : c * c = 1 / 2 := by
    rw [hc, ← mul_inv, sq_sqrt_two]
    norm_num
  fin_cases k <;> fin_cases l <;>
    norm_num [bellCoeff] <;>
    linear_combination (2 : ℂ) * hcc

