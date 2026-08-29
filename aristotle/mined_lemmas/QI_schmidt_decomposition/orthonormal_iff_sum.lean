import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace QI

open Matrix Polynomial Finset
open scoped ComplexConjugate ComplexOrder

variable {m n : ℕ}

/-- The elementary tensor `a ⊗ b` of `a ∈ ℂ^m` and `b ∈ ℂ^n`, viewed inside
`ℂ^m ⊗ ℂ^n ≅ ℂ^(m × n)`. -/

lemma orthonormal_iff_sum {p r : ℕ} (e : Fin r → EuclideanSpace ℂ (Fin p)) :
    Orthonormal ℂ e ↔ ∀ k l, ∑ i, conj (e k i) * e l i = if k = l then 1 else 0 := by
  rw [orthonormal_iff_ite]
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-- The "transposed" form of orthonormality. -/
