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

namespace QPhys

open NormedSpace

section Algebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
  [CompleteSpace A] [StarModule ℂ A]

/-- The time-evolution operator `U(t) = exp (-i H t / ℏ)` associated to a Hamiltonian `H`
in a complex Banach `*`-algebra (e.g. the bounded operators on a Hilbert space). -/

theorem smul_mem_skewAdjoint_of_isSelfAdjoint (hbar : ℝ) {H : A} (hH : IsSelfAdjoint H) (t : ℝ) :
    ((-Complex.I) * (t / hbar) : ℂ) • H ∈ skewAdjoint A := by
  rw [skewAdjoint.mem_iff, star_smul, hH.star_eq, ← neg_smul]
  congr 1
  simp

/-- **Unitarity of time evolution**: for a self-adjoint Hamiltonian `H`, the operator
`U(t) = exp (-i H t / ℏ)` is unitary for every real time `t`. -/
