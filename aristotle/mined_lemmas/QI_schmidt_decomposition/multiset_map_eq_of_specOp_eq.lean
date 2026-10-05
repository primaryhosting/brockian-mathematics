import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Finset Matrix

variable {m n : ℕ}

/-- `IsSchmidtDecomp psi s e f` says that the bipartite pure state `psi` (a vector in
`ℂ^m ⊗ ℂ^n`, written as its coordinate array) has the Schmidt decomposition
`psi = ∑ k, s k • (e k ⊗ f k)`, where the Schmidt coefficients `s k` are strictly positive
and `e`, `f` are orthonormal families in the two factors. -/
structure IsSchmidtDecomp {ι : Type} [Fintype ι] (psi : Fin m → Fin n → ℂ)
    (s : ι → ℝ) (e : ι → EuclideanSpace ℂ (Fin m)) (f : ι → EuclideanSpace ℂ (Fin n)) :
    Prop where
  coeff_pos : ∀ k, 0 < s k
  orthonormal_left : Orthonormal ℂ e
  orthonormal_right : Orthonormal ℂ f
  decomp : ∀ i j, psi i j = ∑ k, (s k : ℂ) * e k i * f k j

/-- The self-adjoint operator `∑ k, c k • ⟪e k, ·⟫ • e k`. -/

lemma multiset_map_eq_of_specOp_eq {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι]
    [DecidableEq ι'] (c : ι → ℝ) (e : ι → EuclideanSpace ℂ (Fin m))
    (c' : ι' → ℝ) (e' : ι' → EuclideanSpace ℂ (Fin m))
    (he : Orthonormal ℂ e) (he' : Orthonormal ℂ e')
    (hc : ∀ k, 0 < c k) (hc' : ∀ k, 0 < c' k)
    (h : specOp c e = specOp c' e') :
    (univ : Finset ι).val.map c = (univ : Finset ι').val.map c' := by
  classical
  have key : ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (d : κ → ℝ) (a : ℝ),
      (Multiset.filter (fun k => a = d k) (univ : Finset κ).val).card
        = (univ.filter (fun k => d k = a)).card := by
    intro κ _ _ d a
    rw [← Finset.filter_val]
    congr 2
    exact Finset.filter_congr (fun k _ => eq_comm)
  refine Multiset.ext.mpr fun a => ?_
  rw [Multiset.count_map, Multiset.count_map, key c a, key c' a]
  rcases lt_or_ge 0 a with ha | ha
  · have h1 := finrank_ker_specOp c e he a (ne_of_gt ha)
    have h2 := finrank_ker_specOp c' e' he' a (ne_of_gt ha)
    rw [← h1, ← h2, h]
  · rw [Finset.filter_false_of_mem
        (fun k _ => by have h1 := hc k; intro hk; rw [hk] at h1; linarith),
      Finset.filter_false_of_mem
        (fun k _ => by have h1 := hc' k; intro hk; rw [hk] at h1; linarith)]
    rfl

/-- The reduced density matrix of `psi` computed from a Schmidt decomposition. -/
