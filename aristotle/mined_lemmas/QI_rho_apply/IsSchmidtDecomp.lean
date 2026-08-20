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

def IsSchmidtDecomp (ψ : EuclideanSpace ℂ (Fin m × Fin n)) (r : ℕ) (σ : Fin r → ℝ)
    (e : Fin r → EuclideanSpace ℂ (Fin m)) (f : Fin r → EuclideanSpace ℂ (Fin n)) : Prop :=
  (∀ k, 0 < σ k) ∧ Orthonormal ℂ e ∧ Orthonormal ℂ f ∧
    ∀ (i : Fin m) (j : Fin n), ψ (i, j) = ∑ k, (σ k : ℂ) * e k i * f k j

