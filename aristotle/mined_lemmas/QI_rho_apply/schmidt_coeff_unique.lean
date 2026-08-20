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

lemma schmidt_coeff_unique {ψ : EuclideanSpace ℂ (Fin m × Fin n)} {r r' : ℕ} {σ : Fin r → ℝ}
    {σ' : Fin r' → ℝ} {e : Fin r → EuclideanSpace ℂ (Fin m)} {f : Fin r → EuclideanSpace ℂ (Fin n)}
    {e' : Fin r' → EuclideanSpace ℂ (Fin m)} {f' : Fin r' → EuclideanSpace ℂ (Fin n)}
    (h : IsSchmidtDecomp ψ r σ e f) (h' : IsSchmidtDecomp ψ r' σ' e' f')
    (ha : Antitone σ) (ha' : Antitone σ') :
    ∃ hr : r = r', ∀ k : Fin r, σ k = σ' (Fin.cast hr k) := by
  have hc := card_filter_eq h h'
  have hms : Multiset.map σ Finset.univ.val = Multiset.map σ' Finset.univ.val := by
    ext a
    rw [Multiset.count_map, Multiset.count_map]
    have e1 : (Multiset.filter (fun k : Fin r => a = σ k) Finset.univ.val).card
        = (Finset.univ.filter (fun k : Fin r => σ k = a)).card := by
      simp [Finset.filter, Finset.card, eq_comm]
    have e2 : (Multiset.filter (fun k : Fin r' => a = σ' k) Finset.univ.val).card
        = (Finset.univ.filter (fun k : Fin r' => σ' k = a)).card := by
      simp [Finset.filter, Finset.card, eq_comm]
    rw [e1, e2, hc a]
  rw [Fin.univ_val_map, Fin.univ_val_map, Multiset.coe_eq_coe] at hms
  have hlen : r = r' := by simpa using hms.length_eq
  subst hlen
  have hsorted : ∀ (s : Fin r → ℝ), Antitone s → List.Pairwise (· ≥ ·) (List.ofFn s) := by
    intro s hs
    rw [List.pairwise_ofFn]
    exact fun i j hij => hs hij.le
  have hL : List.ofFn σ = List.ofFn σ' :=
    List.Perm.eq_of_pairwise (le := (· ≥ ·)) (fun a b _ _ h1 h2 => le_antisymm h2 h1)
      (hsorted σ ha) (hsorted σ' ha') hms
  refine ⟨rfl, fun k => ?_⟩
  have h2 : (List.ofFn σ)[(k : ℕ)]? = (List.ofFn σ')[(k : ℕ)]? := by rw [hL]
  simpa [List.getElem?_ofFn, k.isLt] using h2

