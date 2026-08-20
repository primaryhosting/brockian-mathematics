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

theorem star_mul_timeEvolution (hbar : ℝ) {H : A} (hH : IsSelfAdjoint H) (t : ℝ) :
    star (timeEvolution hbar H t) * timeEvolution hbar H t = 1 ∧
      timeEvolution hbar H t * star (timeEvolution hbar H t) = 1 :=
  Unitary.mem_iff.mp (unitary_time_evolution hbar hH t)

end Algebra

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- On a complex Hilbert space, the time-evolution operator of a self-adjoint (bounded)
Hamiltonian is unitary, i.e. `U(t)† U(t) = U(t) U(t)† = 1`. -/
