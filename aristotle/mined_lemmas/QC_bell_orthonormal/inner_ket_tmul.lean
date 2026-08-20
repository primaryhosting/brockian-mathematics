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

lemma inner_ket_tmul (a b c d : Fin 2) :
    inner ℂ (ket a ⊗ₜ[ℂ] ket b) (ket c ⊗ₜ[ℂ] ket d) = if a = c ∧ b = d then (1 : ℂ) else 0 := by
  rw [TensorProduct.inner_tmul, inner_ket, inner_ket]
  aesop

/- The two lemmas below are instances of `inner_smul_left`/`inner_smul_right`, restated with the
scalar action coming from the tensor product's own module structure so that they are usable as
rewrite rules. -/

