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

def choi (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) : Matrix (n × m) (n × m) ℂ :=
  Matrix.of fun p q => Φ (Matrix.single p.1 q.1 1) p.2 q.2

/-- The ampliation `idₖ ⊗ Φ` of `Φ`, described blockwise: a matrix indexed by `k × n`
is viewed as a `k × k` array of `n × n` blocks, and `Φ` is applied to each block. -/

def ampliation (k : Type) [Fintype k] [DecidableEq k]
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) (X : Matrix (k × n) (k × n) ℂ) :
    Matrix (k × m) (k × m) ℂ :=
  Matrix.of fun p q => Φ (Matrix.of fun i j => X (p.1, i) (q.1, j)) p.2 q.2

/-- `Φ` is completely positive: for every `k`, the ampliation `id_{Fin k} ⊗ Φ` maps
positive semidefinite matrices to positive semidefinite matrices. -/
