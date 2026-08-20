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

lemma exists_antitone_isSchmidtDecomp {ψ : EuclideanSpace ℂ (Fin m × Fin n)} {r : ℕ}
    {σ : Fin r → ℝ} {e : Fin r → EuclideanSpace ℂ (Fin m)} {f : Fin r → EuclideanSpace ℂ (Fin n)}
    (h : IsSchmidtDecomp ψ r σ e f) :
    ∃ (σ' : Fin r → ℝ) (e' : Fin r → EuclideanSpace ℂ (Fin m))
      (f' : Fin r → EuclideanSpace ℂ (Fin n)), IsSchmidtDecomp ψ r σ' e' f' ∧ Antitone σ' := by
  obtain ⟨hpos, he, hf, hdec⟩ := h
  set p : Equiv.Perm (Fin r) := Tuple.sort (fun k => -σ k) with hp
  have hmono : Monotone ((fun k => -σ k) ∘ p) := Tuple.monotone_sort (fun k => -σ k)
  refine ⟨σ ∘ p, e ∘ p, f ∘ p, ⟨fun k => hpos _, he.comp p p.injective, hf.comp p p.injective,
    fun i j => ?_⟩, ?_⟩
  · rw [hdec i j]
    exact (Equiv.sum_comp p (fun k => (σ k : ℂ) * e k i * f k j)).symm
  · intro a b hab
    have := hmono hab
    simpa using neg_le_neg_iff.mp (by simpa using this)

/-- The squared Schmidt coefficients sum to the squared norm of the state. -/
