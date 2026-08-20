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


theorem integral_formula (x : (generator U).domain) (t : ℝ) :
    (I : ℂ) • (∫ s in (0:ℝ)..t, U s (generator U x)) = U t (x : H) - (x : H) := by
  have hint : IntervalIntegrable (fun s : ℝ => (I : ℂ) • U s (generator U x))
      MeasureTheory.volume 0 t :=
    ((continuous_apply hU (generator U x)).const_smul (I : ℂ)).intervalIntegrable 0 t
  have hFTC : ((∫ s in (0:ℝ)..t, (I : ℂ) • U s (generator U x)))
      = (fun s : ℝ => U s (x : H)) t - (fun s : ℝ => U s (x : H)) 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hasDerivAt_of_mem_domain hU x s) hint
  rw [intervalIntegral.integral_smul] at hFTC
  rw [hFTC]
  simp [hU.apply_zero]

/-- If the integrated form of the equation holds, then `x` is in the domain with `A x = z`. -/
