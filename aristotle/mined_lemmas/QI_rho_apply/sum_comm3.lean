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

private lemma sum_comm3 {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] (F : α → β → γ → ℂ) :
    ∑ a, ∑ b, ∑ c, F a b c = ∑ c, ∑ b, ∑ a, F a b c := by
  rw [Finset.sum_comm]
  rw [show (∑ b, ∑ a, ∑ c, F a b c) = ∑ b, ∑ c, ∑ a, F a b c from
    Finset.sum_congr rfl fun b _ => Finset.sum_comm]
  exact Finset.sum_comm

/-- Existence of a Schmidt decomposition (coefficients not yet ordered).  This is the singular
value decomposition of the coefficient matrix, obtained from the spectral decomposition of the
reduced density matrix. -/
