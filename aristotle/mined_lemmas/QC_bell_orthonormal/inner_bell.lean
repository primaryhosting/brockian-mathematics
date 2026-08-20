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

lemma inner_bell (i j : Fin 4) : inner ℂ (bell i) (bell j) = if i = j then (1 : ℂ) else 0 := by
  have h2 : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 2⁻¹ := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Real.sqrt_inv,
      ← Real.sqrt_mul (by positivity)]
    norm_num
  fin_cases i <;> fin_cases j <;>
    simp only [bell, tp_inner_smul_left, tp_inner_smul_right, inner_add_left, inner_add_right,
      inner_sub_left, inner_sub_right, inner_ket_tmul, ← Complex.ofReal_inv,
      Complex.conj_ofReal] <;>
    norm_num <;>
    linear_combination (2 : ℂ) * h2

/-- The four Bell states form an orthonormal family in `ℂ² ⊗ ℂ²`. -/
