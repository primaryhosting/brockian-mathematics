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

lemma finrank_eigenspace_of_decomp {ψ : EuclideanSpace ℂ (Fin m × Fin n)} {r : ℕ} {σ : Fin r → ℝ}
    {e : Fin r → EuclideanSpace ℂ (Fin m)} {f : Fin r → EuclideanSpace ℂ (Fin n)}
    (h : IsSchmidtDecomp ψ r σ e f) {t : ℝ} (ht : t ≠ 0) :
    Module.finrank ℂ (Module.End.eigenspace (Matrix.toEuclideanLin (rho ψ)) (t : ℂ)) =
      (Finset.univ.filter (fun k : Fin r => σ k ^ 2 = t)).card := by
  rw [eigenspace_eq_span h ht]
  have hli : LinearIndependent ℂ (fun k : {k : Fin r // σ k ^ 2 = t} => e (k : Fin r)) :=
    (h.2.1.comp _ Subtype.val_injective).linearIndependent
  rw [finrank_span_eq_card hli, Fintype.card_subtype]

/-- Two Schmidt decompositions of the same vector have the same number of coefficients with any
prescribed value. -/
