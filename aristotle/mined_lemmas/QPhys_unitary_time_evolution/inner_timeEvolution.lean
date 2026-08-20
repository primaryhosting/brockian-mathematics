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

theorem inner_timeEvolution (hbar : ℝ) {H : E →L[ℂ] E} (hH : IsSelfAdjoint H) (t : ℝ)
    (x y : E) :
    inner ℂ (timeEvolution hbar H t x) (timeEvolution hbar H t y) = inner ℂ x y := by
  have h := (Unitary.mem_iff.mp (unitary_time_evolution_clm hbar hH t)).1
  have : (ContinuousLinearMap.adjoint (timeEvolution hbar H t)).comp
      (timeEvolution hbar H t) = ContinuousLinearMap.id ℂ E := h
  calc inner ℂ (timeEvolution hbar H t x) (timeEvolution hbar H t y)
      = inner ℂ x (ContinuousLinearMap.adjoint (timeEvolution hbar H t)
          (timeEvolution hbar H t y)) := by
        rw [ContinuousLinearMap.adjoint_inner_right]
    _ = inner ℂ x y := by
        rw [show ContinuousLinearMap.adjoint (timeEvolution hbar H t)
            (timeEvolution hbar H t y) = y from congrArg (fun f => f y) this]

/-- Time evolution is norm preserving. -/
