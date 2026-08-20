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

theorem schmidt_coefficients_unique {ι κ : Type} [Fintype ι] [Fintype κ]
    {psi : EuclideanSpace ℂ (Fin m × Fin n)} {σ : ι → ℝ}
    {u : ι → EuclideanSpace ℂ (Fin m)} {v : ι → EuclideanSpace ℂ (Fin n)} {τ : κ → ℝ}
    {u' : κ → EuclideanSpace ℂ (Fin m)} {v' : κ → EuclideanSpace ℂ (Fin n)}
    (h : IsSchmidtDecomposition psi σ u v) (h' : IsSchmidtDecomposition psi τ u' v') :
    (Finset.univ.val.map σ) = (Finset.univ.val.map τ) := by
  classical
  have hT1 : ∀ x, (Matrix.toEuclideanLin (reducedLeft psi)) x
      = ∑ k, ((σ k ^ 2 : ℝ) : ℂ) • (⟪u k, x⟫_ℂ • u k) :=
    fun x => toEuclideanLin_reducedLeft_of_schmidt h x
  have hT2 : ∀ x, (Matrix.toEuclideanLin (reducedLeft psi)) x
      = ∑ k, ((τ k ^ 2 : ℝ) : ℂ) • (⟪u' k, x⟫_ℂ • u' k) :=
    fun x => toEuclideanLin_reducedLeft_of_schmidt h' x
  refine Multiset.ext.mpr fun a => ?_
  rcases le_or_gt a 0 with hle | hpos
  · have e1 : ∀ {J : Type} [Fintype J] (f : J → ℝ), (∀ k, 0 < f k) →
        Multiset.count a (Multiset.map f Finset.univ.val) = 0 := by
      intro J _ f hf
      refine Multiset.count_eq_zero.mpr ?_
      simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and, not_exists]
      intro k hk
      exact absurd (hk ▸ hf k) (not_lt.mpr hle)
    rw [e1 σ h.coeff_pos, e1 τ h'.coeff_pos]
  · have c1 : ∀ {J : Type} [Fintype J] (f : J → ℝ), (∀ k, 0 < f k) →
        Multiset.count a (Multiset.map f Finset.univ.val) = #{k | f k ^ 2 = a ^ 2} := by
      intro J _ f hf
      rw [Multiset.count_map]
      have hfin : Finset.filter (fun k => a = f k) Finset.univ
          = Finset.filter (fun k => f k ^ 2 = a ^ 2) Finset.univ := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro rfl; ring
        · intro hk
          have := hf k
          nlinarith [sq_nonneg (f k - a), sq_nonneg (f k + a)]
      calc (Multiset.filter (fun k => a = f k) Finset.univ.val).card
          = #{k | a = f k} := rfl
        _ = #{k | f k ^ 2 = a ^ 2} := by rw [hfin]
    have ha2 : (0 : ℝ) < a ^ 2 := by positivity
    rw [c1 σ h.coeff_pos, c1 τ h'.coeff_pos,
      ← finrank_eigenspace_of_spectral h.left_orthonormal _ hT1 ha2,
      ← finrank_eigenspace_of_spectral h'.left_orthonormal _ hT2 ha2]

/-- **Schmidt decomposition.** Every bipartite pure state `psi ∈ ℂ^m ⊗ ℂ^n` admits a Schmidt
decomposition `psi = ∑ k, σ k • (u k ⊗ v k)` with positive Schmidt coefficients `σ k` and
orthonormal families `u`, `v`; moreover the Schmidt coefficients are unique: any two Schmidt
decompositions have the same multiset of coefficients (hence the same Schmidt rank). -/
