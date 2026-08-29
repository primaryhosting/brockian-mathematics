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

lemma schmidt_rank_le {psi : EuclideanSpace ℂ (Fin m × Fin n)} {r : ℕ} {lam : Fin r → ℝ}
    {e : Fin r → EuclideanSpace ℂ (Fin m)} {f : Fin r → EuclideanSpace ℂ (Fin n)}
    (h : IsSchmidtDecomposition psi r lam e f) : r ≤ m := by
  simpa using h.left_orthonormal.linearIndependent.fintype_card_le_finrank (R := ℂ)

/-- Splitting `Fin m` as `Fin r ⊕ Fin (m - r)`. -/
