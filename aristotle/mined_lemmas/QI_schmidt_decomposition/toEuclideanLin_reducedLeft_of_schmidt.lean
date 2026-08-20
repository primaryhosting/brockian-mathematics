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

lemma toEuclideanLin_reducedLeft_of_schmidt (h : IsSchmidtDecomposition psi σ u v)
    (x : EuclideanSpace ℂ (Fin m)) :
    Matrix.toEuclideanLin (reducedLeft psi) x =
      ∑ k, ((σ k ^ 2 : ℝ) : ℂ) • (⟪u k, x⟫_ℂ • u k) := by
  refine PiLp.ext fun i => ?_
  have hlhs : (Matrix.toEuclideanLin (reducedLeft psi) x) i = ∑ a, reducedLeft psi i a * x a := by
    simp [Matrix.toEuclideanLin, Matrix.mulVec, dotProduct]
  have hrhs : ((∑ k, ((σ k ^ 2 : ℝ) : ℂ) • (⟪u k, x⟫_ℂ • u k) : EuclideanSpace ℂ (Fin m))) i
      = ∑ k, ((σ k ^ 2 : ℝ) : ℂ) * (⟪u k, x⟫_ℂ * u k i) := by
    simp
  rw [hlhs, hrhs]
  simp only [fun a => reducedLeft_of_schmidt h i a, inner_euclidean, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- The eigenspace for a positive eigenvalue `t` of an operator given in "spectral" form
`T x = ∑ k, c k • ⟪u k, x⟫ • u k` with `u` orthonormal and `c` positive is spanned by the
`u k` with `c k = t`; in particular its dimension is the number of such `k`. -/
