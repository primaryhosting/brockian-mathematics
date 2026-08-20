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


theorem mem_domain_of_integral_eq (x z : H)
    (h : ∀ t : ℝ, U t x - x = (I : ℂ) • ∫ s in (0:ℝ)..t, U s z) :
    ∃ hx : x ∈ (generator U).domain, generator U ⟨x, hx⟩ = z := by
  have hF : HasDerivAt (fun t : ℝ => ∫ s in (0:ℝ)..t, U s z) (U 0 z) 0 :=
    intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_apply hU z 0 0)
      ((continuous_apply hU z).stronglyMeasurableAtFilter _ _)
      (continuous_apply hU z).continuousAt
  have hF' : HasDerivAt (fun t : ℝ => ∫ s in (0:ℝ)..t, U s z) z 0 := by
    rw [hU.apply_zero] at hF
    simpa using hF
  have hderiv : HasDerivAt (fun t : ℝ => x + (I : ℂ) • ∫ s in (0:ℝ)..t, U s z)
      ((I : ℂ) • z) 0 := by
    simpa using (hF'.const_smul (I : ℂ)).const_add x
  have hfun : (fun t : ℝ => x + (I : ℂ) • ∫ s in (0:ℝ)..t, U s z)
      = fun t : ℝ => U t x := by
    funext t
    rw [← h t]
    abel
  rw [hfun] at hderiv
  exact ⟨mem_generator_domain hderiv, generator_apply_eq _ hderiv⟩

/-- The averages `e⁻¹ • ∫_0^e U s x ds` belong to the domain of the generator. -/
