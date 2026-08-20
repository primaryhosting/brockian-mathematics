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

lemma rho_apply_of_decomp {ψ : EuclideanSpace ℂ (Fin m × Fin n)} {r : ℕ} {σ : Fin r → ℝ}
    {e : Fin r → EuclideanSpace ℂ (Fin m)} {f : Fin r → EuclideanSpace ℂ (Fin n)}
    (h : IsSchmidtDecomp ψ r σ e f) (i i' : Fin m) :
    rho ψ i i' = ∑ k, ((σ k ^ 2 : ℝ) : ℂ) * e k i * conj (e k i') := by
  obtain ⟨hpos, he, hf, hdec⟩ := h
  rw [rho_apply]
  have key : ∀ j : Fin n, ψ (i, j) * conj (ψ (i', j))
      = ∑ k, ∑ l, ((σ k : ℂ) * e k i * ((σ l : ℂ) * conj (e l i'))) * (f k j * conj (f l j)) := by
    intro j
    rw [hdec i j, hdec i' j, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [map_mul, Complex.conj_ofReal]
    ring
  simp only [key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  have hsum : ∀ l : Fin r,
      ∑ j, ((σ k : ℂ) * e k i * ((σ l : ℂ) * conj (e l i'))) * (f k j * conj (f l j))
        = ((σ k : ℂ) * e k i * ((σ l : ℂ) * conj (e l i'))) * (if k = l then 1 else 0) := by
    intro l
    rw [← Finset.mul_sum, orth_sum hf]
  simp only [hsum]
  simp [Finset.sum_ite_eq]
  ring

/-- The action of the reduced density matrix, expressed through a Schmidt decomposition. -/
