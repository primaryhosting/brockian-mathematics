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


theorem norm_integral_sub_le (a b : H) (t : ℝ) :
    ‖(∫ s in (0:ℝ)..t, U s a) - ∫ s in (0:ℝ)..t, U s b‖ ≤ ‖a - b‖ * |t| := by
  rw [← intervalIntegral.integral_sub (intervalIntegrable_apply hU a 0 t)
    (intervalIntegrable_apply hU b 0 t)]
  have hfun : ∀ s : ℝ, U s a - U s b = U s (a - b) := by
    intro s; simp [map_sub]
  simp_rw [hfun]
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := t)
    (C := ‖a - b‖) (f := fun s : ℝ => U s (a - b)) (fun s _ => le_of_eq (hU.norm_map s (a - b)))
  simpa using hle

