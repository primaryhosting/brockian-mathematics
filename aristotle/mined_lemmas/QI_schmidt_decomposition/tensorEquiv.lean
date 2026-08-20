import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Statement: Every bipartite pure state has a Schmidt decomposition with unique Schmidt coefficients.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix

namespace QI

/-! ### Power sums determine a finite multiset of positive reals -/

open Polynomial in
/-- If two multisets of positive reals have the same power sums `∑ xᵏ` for every `k ≥ 1`,
they are equal. -/

noncomputable def tensorEquiv (m n : ℕ) :
    (EuclideanSpace ℂ (Fin m) ⊗[ℂ] EuclideanSpace ℂ (Fin n)) ≃ₗ[ℂ]
      EuclideanSpace ℂ (Fin m × Fin n) :=
  ((EuclideanSpace.basisFun (Fin m) ℂ).toBasis.tensorProduct
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis).equivFun ≪≫ₗ
    (WithLp.linearEquiv 2 ℂ (Fin m × Fin n → ℂ)).symm

open TensorProduct in
