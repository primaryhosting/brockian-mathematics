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


theorem tendsto_integral_of_tendsto {v : ℕ → H} {w : H} (t : ℝ)
    (hv : Filter.Tendsto v Filter.atTop (nhds w)) :
    Filter.Tendsto (fun n => ∫ s in (0:ℝ)..t, U s (v n)) Filter.atTop
      (nhds (∫ s in (0:ℝ)..t, U s w)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _)
    (fun n => norm_integral_sub_le hU (v n) w t) ?_
  have h0 : Filter.Tendsto (fun n => ‖v n - w‖) Filter.atTop (nhds 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hv
  simpa using h0.mul_const |t|

/-- The generator is a closed operator. -/
