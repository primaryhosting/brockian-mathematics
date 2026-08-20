import Mathlib

/-!
# Bell Orthonormal
Category: Quantum Computing
Target: QC.bell_orthonormal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
The four Bell states

  Φ⁺ = (|00⟩ + |11⟩)/√2,   Φ⁻ = (|00⟩ - |11⟩)/√2,
  Ψ⁺ = (|01⟩ + |10⟩)/√2,   Ψ⁻ = (|01⟩ - |10⟩)/√2

form an orthonormal basis of the two-qubit space ℂ² ⊗ ℂ².

The main statement `QC.bell_orthonormal` is formalised in the genuine tensor product
`EuclideanSpace ℂ (Fin 2) ⊗[ℂ] EuclideanSpace ℂ (Fin 2)`, carrying Mathlib's inner product
space structure on a tensor product of inner product spaces.  A second, coordinate version
on `EuclideanSpace ℂ (Fin 2 × Fin 2)` is given at the end of the file.
-/

namespace QC

open scoped TensorProduct ComplexConjugate

/-! ## The two-qubit space as a tensor product -/

/-- A single qubit: the Hilbert space `ℂ²`. -/
abbrev Qubit := EuclideanSpace ℂ (Fin 2)

/-- The computational basis vectors `|0⟩` and `|1⟩` of a single qubit. -/

theorem bellVec_orthonormal_family : Orthonormal ℂ bellVec := by
  constructor
  · intro i
    rw [EuclideanSpace.norm_eq]
    fin_cases i <;>
      simp [bellVec, bellRaw, Fintype.sum_prod_type, Fin.sum_univ_succ, Complex.norm_real] <;>
      rw [show (2 : ℝ)⁻¹ + 2⁻¹ = 1 by norm_num]
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [bellVec, bellRaw, PiLp.inner_apply, Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- The four Bell states form an orthonormal basis of `EuclideanSpace ℂ (Fin 2 × Fin 2)`. -/
