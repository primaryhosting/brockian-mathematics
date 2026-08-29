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

@[simp] lemma tensor_apply (a : EuclideanSpace ℂ (Fin m)) (b : EuclideanSpace ℂ (Fin n))
    (p : Fin m × Fin n) : tensor a b p = a p.1 * b p.2 := rfl

/-- `IsSchmidtDecomposition psi r lam e f` says that the bipartite pure state `psi` is written
as `∑ k, lam k • (e k ⊗ f k)` where the `lam k` are strictly positive reals (the Schmidt
coefficients) and `e`, `f` are orthonormal families in the two factors. -/
structure IsSchmidtDecomposition (psi : EuclideanSpace ℂ (Fin m × Fin n))
    (r : ℕ) (lam : Fin r → ℝ) (e : Fin r → EuclideanSpace ℂ (Fin m))
    (f : Fin r → EuclideanSpace ℂ (Fin n)) : Prop where
  coeff_pos : ∀ k, 0 < lam k
  left_orthonormal : Orthonormal ℂ e
  right_orthonormal : Orthonormal ℂ f
  decomp : psi = ∑ k, (lam k : ℂ) • tensor (e k) (f k)

/-- Orthonormality of a family in `EuclideanSpace ℂ (Fin p)` in coordinates. -/
