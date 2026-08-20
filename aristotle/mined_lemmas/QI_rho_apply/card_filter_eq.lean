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

lemma card_filter_eq {ψ : EuclideanSpace ℂ (Fin m × Fin n)} {r r' : ℕ} {σ : Fin r → ℝ}
    {σ' : Fin r' → ℝ} {e : Fin r → EuclideanSpace ℂ (Fin m)} {f : Fin r → EuclideanSpace ℂ (Fin n)}
    {e' : Fin r' → EuclideanSpace ℂ (Fin m)} {f' : Fin r' → EuclideanSpace ℂ (Fin n)}
    (h : IsSchmidtDecomp ψ r σ e f) (h' : IsSchmidtDecomp ψ r' σ' e' f') (t : ℝ) :
    (Finset.univ.filter (fun k : Fin r => σ k = t)).card =
      (Finset.univ.filter (fun k : Fin r' => σ' k = t)).card := by
  rcases le_or_gt t 0 with hle | hpos
  · have e1 : (Finset.univ.filter (fun k : Fin r => σ k = t)) = ∅ := by
      refine Finset.filter_false_of_mem fun k _ hk => ?_
      exact absurd (hk ▸ h.1 k) (not_lt.mpr hle)
    have e2 : (Finset.univ.filter (fun k : Fin r' => σ' k = t)) = ∅ := by
      refine Finset.filter_false_of_mem fun k _ hk => ?_
      exact absurd (hk ▸ h'.1 k) (not_lt.mpr hle)
    rw [e1, e2, Finset.card_empty, Finset.card_empty]
  · have hsq : ∀ (s : ℝ), 0 < s → (s ^ 2 = t ^ 2 ↔ s = t) := by
      intro s hs
      constructor
      · intro hst; nlinarith
      · intro hst; rw [hst]
    have e1 : (Finset.univ.filter (fun k : Fin r => σ k = t))
        = (Finset.univ.filter (fun k : Fin r => σ k ^ 2 = t ^ 2)) := by
      refine Finset.filter_congr fun k _ => ?_
      simp [hsq (σ k) (h.1 k)]
    have e2 : (Finset.univ.filter (fun k : Fin r' => σ' k = t))
        = (Finset.univ.filter (fun k : Fin r' => σ' k ^ 2 = t ^ 2)) := by
      refine Finset.filter_congr fun k _ => ?_
      simp [hsq (σ' k) (h'.1 k)]
    have ht2 : t ^ 2 ≠ 0 := by positivity
    rw [e1, e2, ← finrank_eigenspace_of_decomp h ht2, ← finrank_eigenspace_of_decomp h' ht2]

/-- Uniqueness of the Schmidt coefficients (listed in decreasing order). -/
