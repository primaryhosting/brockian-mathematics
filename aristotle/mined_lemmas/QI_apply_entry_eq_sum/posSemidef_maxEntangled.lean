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

open Matrix
open scoped ComplexOrder

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The Choi matrix of a linear map `Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ`.
It is the block matrix `∑ i j, Eᵢⱼ ⊗ Φ Eᵢⱼ`, written entrywise as
`choiMatrix Φ (i, a) (j, b) = Φ (single i j 1) a b`. -/

lemma posSemidef_maxEntangled :
    (Matrix.of fun p q : n × n => (if p.1 = p.2 then (1 : ℂ) else 0) *
      (if q.1 = q.2 then (1 : ℂ) else 0)).PosSemidef := by
  have h : (Matrix.of fun p q : n × n => (if p.1 = p.2 then (1 : ℂ) else 0) *
      (if q.1 = q.2 then (1 : ℂ) else 0))
      = (Matrix.of fun (p : n × n) (_ : Unit) => (if p.1 = p.2 then (1 : ℂ) else 0)) *
        (Matrix.of fun (p : n × n) (_ : Unit) => (if p.1 = p.2 then (1 : ℂ) else 0))ᴴ := by
    ext p q
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [h]
  exact Matrix.posSemidef_self_mul_conjTranspose _

omit [DecidableEq m] in
/-- **Choi–Jamiołkowski isomorphism**: a linear map between matrix algebras is completely
positive if and only if its Choi matrix is positive semidefinite. -/
