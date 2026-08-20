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

/-!
# Stone's theorem

A strongly continuous one-parameter unitary group `U : ℝ → (H →L[ℂ] H)` on a complex Hilbert
space `H` has a self-adjoint (in general unbounded) generator `A`, characterized by
`d/dt (U t x) |_{t=0} = i • A x`.
-/

namespace QPhys

open scoped InnerProductSpace
open Complex (I)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A strongly continuous one-parameter unitary group on a complex Hilbert space. -/
structure IsUnitaryGroup (U : ℝ → (H →L[ℂ] H)) : Prop where
  /-- Each `U t` is a unitary operator. -/
  mem_unitary : ∀ t, U t ∈ unitary (H →L[ℂ] H)
  /-- The group law. -/
  map_add : ∀ s t : ℝ, U (s + t) = U s * U t
  /-- Strong continuity. -/
  strong_continuous : ∀ x : H, Continuous fun t => U t x

namespace IsUnitaryGroup

variable {U : ℝ → (H →L[ℂ] H)} (hU : IsUnitaryGroup U)
include hU


theorem hasDerivAt_comp_left (x : (generator U).domain) (t : ℝ) :
    HasDerivAt (fun s : ℝ => U s (U t (x : H))) (I • U t (generator U x)) 0 := by
  have h0 := hasDerivAt_generator U x
  have h1 : HasDerivAt (fun s : ℝ => U t (U s (x : H))) (U t (I • generator U x)) 0 :=
    clm_hasDerivAt (U t) h0
  have hcomm : (fun s : ℝ => U t (U s (x : H))) = fun s : ℝ => U s (U t (x : H)) := by
    funext s
    have h2 : U t * U s = U s * U t := by
      rw [← hU.map_add, ← hU.map_add, add_comm]
    have := congrArg (fun L : H →L[ℂ] H => L (x : H)) h2
    exact this
  rw [hcomm] at h1
  simpa [map_smul] using h1

