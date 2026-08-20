import Mathlib

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

namespace QI

open Finset Matrix ComplexConjugate

variable {m n : ℕ}

/-- The coefficient matrix of a bipartite vector `ψ ∈ ℂ^m ⊗ ℂ^n`, where the tensor product is
modelled as `EuclideanSpace ℂ (Fin m × Fin n)`. -/

lemma sum_sq_eq_norm_sq {ψ : EuclideanSpace ℂ (Fin m × Fin n)} {r : ℕ} {σ : Fin r → ℝ}
    {e : Fin r → EuclideanSpace ℂ (Fin m)} {f : Fin r → EuclideanSpace ℂ (Fin n)}
    (h : IsSchmidtDecomp ψ r σ e f) : ∑ k, σ k ^ 2 = ‖ψ‖ ^ 2 := by
  obtain ⟨hpos, he, hf, hdec⟩ := h
  have hone : ∀ k, ∑ i, ((σ k ^ 2 : ℝ) : ℂ) * e k i * conj (e k i) = ((σ k ^ 2 : ℝ) : ℂ) := by
    intro k
    have hk : ∑ i, e k i * conj (e k i) = 1 := by simpa using orth_sum he k k
    calc ∑ i, ((σ k ^ 2 : ℝ) : ℂ) * e k i * conj (e k i)
        = ((σ k ^ 2 : ℝ) : ℂ) * ∑ i, e k i * conj (e k i) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      _ = ((σ k ^ 2 : ℝ) : ℂ) := by rw [hk, mul_one]
  have h1 : ∑ i, rho ψ i i = ((∑ k, σ k ^ 2 : ℝ) : ℂ) := by
    simp only [rho_apply_of_decomp ⟨hpos, he, hf, hdec⟩]
    rw [Finset.sum_comm, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun k _ => hone k
  have h2 : ∑ i, rho ψ i i = ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
    simp only [rho_apply]
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    push_cast
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.mul_conj]
    norm_cast
    exact Complex.normSq_eq_norm_sq _
  exact_mod_cast h1.symm.trans h2

/-- **Schmidt decomposition.**  Every bipartite pure state `ψ` in `ℂ^m ⊗ ℂ^n` (modelled as
`EuclideanSpace ℂ (Fin m × Fin n)`) can be written as `ψ = ∑ k, σ k • (e k ⊗ f k)` for a positive,
decreasing family of real Schmidt coefficients `σ` and orthonormal families `e`, `f` in the two
factors; the squared coefficients sum to `1`.  Moreover the Schmidt coefficients are unique: any
two such decompositions have the same number of terms and the same (decreasingly ordered)
coefficients. -/
