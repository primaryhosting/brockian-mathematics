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
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

open Finset Matrix
open scoped ComplexConjugate InnerProductSpace

namespace QI

variable {m n : ℕ}

/-- `IsSchmidtDecomposition psi σ u v` says that the bipartite pure state `psi`, a vector of the
tensor product `ℂ^m ⊗ ℂ^n` realized as `EuclideanSpace ℂ (Fin m × Fin n)`, is written as
`psi = ∑ k, σ k • (u k ⊗ v k)` where the `σ k` are strictly positive reals (the Schmidt
coefficients) and `u`, `v` are orthonormal families in the two factors. -/
structure IsSchmidtDecomposition {ι : Type} [Fintype ι]
    (psi : EuclideanSpace ℂ (Fin m × Fin n)) (σ : ι → ℝ)
    (u : ι → EuclideanSpace ℂ (Fin m)) (v : ι → EuclideanSpace ℂ (Fin n)) : Prop where
  coeff_pos : ∀ k, 0 < σ k
  left_orthonormal : Orthonormal ℂ u
  right_orthonormal : Orthonormal ℂ v
  sum_eq : ∀ i j, psi (i, j) = ∑ k, (σ k : ℂ) * u k i * v k j

/-- The matrix of coefficients of a bipartite state in the product basis. -/

theorem schmidt_decomposition (psi : EuclideanSpace ℂ (Fin m × Fin n)) :
    (∃ (r : ℕ) (σ : Fin r → ℝ) (u : Fin r → EuclideanSpace ℂ (Fin m))
        (v : Fin r → EuclideanSpace ℂ (Fin n)), IsSchmidtDecomposition psi σ u v) ∧
      (∀ (r r' : ℕ) (σ : Fin r → ℝ) (u : Fin r → EuclideanSpace ℂ (Fin m))
          (v : Fin r → EuclideanSpace ℂ (Fin n)) (τ : Fin r' → ℝ)
          (u' : Fin r' → EuclideanSpace ℂ (Fin m)) (v' : Fin r' → EuclideanSpace ℂ (Fin n)),
        IsSchmidtDecomposition psi σ u v → IsSchmidtDecomposition psi τ u' v' →
          r = r' ∧ (Finset.univ.val.map σ) = (Finset.univ.val.map τ)) := by
  refine ⟨exists_schmidtDecomposition psi, ?_⟩
  intro r r' σ u v τ u' v' h h'
  have hm := schmidt_coefficients_unique h h'
  refine ⟨?_, hm⟩
  have := congrArg Multiset.card hm
  simpa using this

end QI

