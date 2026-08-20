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

lemma reducedLeft_of_schmidt (h : IsSchmidtDecomposition psi σ u v) (i a : Fin m) :
    reducedLeft psi i a = ∑ k, ((σ k ^ 2 : ℝ) : ℂ) * u k i * conj (u k a) := by
  classical
  have hv : ∀ k l, (∑ j, v k j * conj (v l j)) = if l = k then 1 else 0 := by
    intro k l
    have hkl := orthonormal_iff_ite.mp h.right_orthonormal l k
    rw [inner_euclidean] at hkl
    rw [← hkl]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [reducedLeft_apply]
  have step : ∀ j : Fin n, psi (i, j) * conj (psi (a, j))
      = ∑ k, ∑ l, ((σ k : ℂ) * u k i * ((σ l : ℂ) * conj (u l a))) * (v k j * conj (v l j)) := by
    intro j
    rw [h.sum_eq i j, h.sum_eq a j, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [map_mul, Complex.conj_ofReal]
    ring
  simp only [step]
  have swap : ∑ j, ∑ k, ∑ l, ((σ k : ℂ) * u k i * ((σ l : ℂ) * conj (u l a)))
        * (v k j * conj (v l j))
      = ∑ k, ∑ l, ((σ k : ℂ) * u k i * ((σ l : ℂ) * conj (u l a)))
        * (∑ j, v k j * conj (v l j)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => (Finset.mul_sum _ _ _).symm
  rw [swap]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [hv]
  rw [Finset.sum_eq_single k]
  · rw [if_pos rfl]
    push_cast
    ring
  · intro l _ hl
    rw [if_neg hl, mul_zero]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- The operator associated with the reduced density matrix, in terms of a Schmidt
decomposition. -/
