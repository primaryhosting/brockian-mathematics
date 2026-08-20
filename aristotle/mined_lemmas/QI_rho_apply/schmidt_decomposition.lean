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

theorem schmidt_decomposition (ψ : EuclideanSpace ℂ (Fin m × Fin n)) (hψ : ‖ψ‖ = 1) :
    (∃ (r : ℕ) (σ : Fin r → ℝ) (e : Fin r → EuclideanSpace ℂ (Fin m))
        (f : Fin r → EuclideanSpace ℂ (Fin n)),
        IsSchmidtDecomp ψ r σ e f ∧ Antitone σ ∧ ∑ k, σ k ^ 2 = 1) ∧
      (∀ (r r' : ℕ) (σ : Fin r → ℝ) (σ' : Fin r' → ℝ)
        (e : Fin r → EuclideanSpace ℂ (Fin m)) (f : Fin r → EuclideanSpace ℂ (Fin n))
        (e' : Fin r' → EuclideanSpace ℂ (Fin m)) (f' : Fin r' → EuclideanSpace ℂ (Fin n)),
        IsSchmidtDecomp ψ r σ e f → Antitone σ → IsSchmidtDecomp ψ r' σ' e' f' → Antitone σ' →
        ∃ hr : r = r', ∀ k : Fin r, σ k = σ' (Fin.cast hr k)) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨r, σ₀, e₀, f₀, h₀⟩ := exists_isSchmidtDecomp ψ
    obtain ⟨σ, e, f, h, hanti⟩ := exists_antitone_isSchmidtDecomp h₀
    exact ⟨r, σ, e, f, h, hanti, by rw [sum_sq_eq_norm_sq h, hψ, one_pow]⟩
  · intro r r' σ σ' e f e' f' h ha h' ha'
    exact schmidt_coeff_unique h h' ha ha'

end QI

