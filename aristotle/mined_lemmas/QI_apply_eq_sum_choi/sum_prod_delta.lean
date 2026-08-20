import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

open Matrix

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The Choi matrix of a linear map `Φ` between matrix algebras:
`C(Φ) (i, α) (j, β) = Φ (Eᵢⱼ) α β`, where `Eᵢⱼ` is the matrix unit. -/

theorem sum_prod_delta {k n' : Type} [Fintype k] [Fintype n'] [DecidableEq k] (p : k)
    (c : k → n' → ℂ) : ∑ r, ∑ i, (if p = r then c r i else 0) = ∑ i, c p i := by
  rw [Finset.sum_comm]; simp

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
/-- Entries of `A * X * Aᴴ` where `A` is the block-diagonal ampliation `I ⊗ K` of `K`. -/
