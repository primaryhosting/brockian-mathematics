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


theorem genGraph_fst_eq_zero (U : ℝ → (H →L[ℂ] H)) :
    ∀ p ∈ genGraph U, p.1 = 0 → p.2 = 0 := by
  intro p hp h1
  rw [mem_genGraph_iff] at hp
  rw [h1] at hp
  have hzero : HasDerivAt (fun _ : ℝ => U 0 0) (0 : H) 0 := by
    simpa using (hasDerivAt_const (0:ℝ) (U 0 0))
  have hp' : HasDerivAt (fun _ : ℝ => (0:H)) (I • p.2) 0 := by
    simpa using hp
  have : I • p.2 = 0 := by
    have h0 : HasDerivAt (fun _ : ℝ => (0:H)) (0:H) 0 := by
      simpa using (hasDerivAt_const (0:ℝ) (0:H))
    exact hp'.unique h0
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  exact (smul_eq_zero.mp this).resolve_left hI

/-- The generator of a one-parameter unitary group, as an unbounded (partially defined)
operator. -/
