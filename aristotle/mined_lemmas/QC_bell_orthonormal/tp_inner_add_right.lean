import Mathlib

/-!
# Bell Orthonormal
Category: Quantum Computing
Target: QC.bell_orthonormal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped TensorProduct

namespace QC

/-- A single qubit space `ℂ²`, with its Hermitian (Euclidean) inner product. -/
abbrev Qubit : Type := EuclideanSpace ℂ (Fin 2)

/-- The two-qubit space `ℂ² ⊗ ℂ²`. Mathlib's inner product on a tensor product of inner
product spaces is determined by `⟪a ⊗ b, c ⊗ d⟫ = ⟪a, c⟫ * ⟪b, d⟫`
(`TensorProduct.instInnerProductSpace`). -/
abbrev TwoQubit : Type := Qubit ⊗[ℂ] Qubit

/-- The computational basis kets `|0⟩`, `|1⟩` of a single qubit. -/

lemma tp_inner_add_right (x y z : TwoQubit) :
    inner ℂ x (y + z) = inner ℂ x y + inner ℂ x z := inner_add_right x y z

/-- A normalized two-term combination `(|ab⟩ + s • |cd⟩)/√2` of computational basis states.
Each Bell state is of this shape with `s = ±1`. -/
