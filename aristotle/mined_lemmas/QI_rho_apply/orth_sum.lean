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

lemma orth_sum {N r : ℕ} {g : Fin r → EuclideanSpace ℂ (Fin N)} (hg : Orthonormal ℂ g)
    (k l : Fin r) : ∑ j, g k j * conj (g l j) = if k = l then 1 else 0 := by
  have h1 := (orthonormal_iff_ite.mp hg) k l
  rw [inner_eq_sum] at h1
  have h2 := congrArg (starRingEnd ℂ) h1
  simp only [map_sum, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply] at h2
  rw [h2]
  by_cases h : k = l <;> simp [h]

/-- The reduced density matrix expressed through a Schmidt decomposition. -/
