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


theorem average_mem_domain (x : H) (e : ℝ) :
    ((e⁻¹ : ℝ) • ∫ s in (0:ℝ)..e, U s x) ∈ (generator U).domain := by
  set F : ℝ → H := fun u => ∫ s in (0:ℝ)..u, U s x with hFdef
  have hFderiv : ∀ u : ℝ, HasDerivAt F (U u x) u := by
    intro u
    exact intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_apply hU x 0 u)
      ((continuous_apply hU x).stronglyMeasurableAtFilter _ _)
      (continuous_apply hU x).continuousAt
  have hkey : ∀ t : ℝ, U t ((e⁻¹ : ℝ) • ∫ s in (0:ℝ)..e, U s x)
      = (e⁻¹ : ℝ) • (F (e + t) - F t) := by
    intro t
    have h1 : U t ((e⁻¹ : ℝ) • ∫ s in (0:ℝ)..e, U s x)
        = (e⁻¹ : ℝ) • U t (∫ s in (0:ℝ)..e, U s x) := by
      simp
    have h2 : U t (∫ s in (0:ℝ)..e, U s x) = ∫ s in (0:ℝ)..e, U t (U s x) :=
      (ContinuousLinearMap.intervalIntegral_comp_comm (U t) (intervalIntegrable_apply hU x 0 e)).symm
    have h3 : ∀ s : ℝ, U t (U s x) = U (s + t) x := by
      intro s
      have : U s * U t = U (s + t) := (hU.map_add s t).symm
      have hc : U t * U s = U (s + t) := by
        rw [← hU.map_add, add_comm]
      exact congrArg (fun L : H →L[ℂ] H => L x) hc
    have h4 : (∫ s in (0:ℝ)..e, U t (U s x)) = ∫ s in (0:ℝ)..e, U (s + t) x := by
      simp_rw [h3]
    have h5 : (∫ s in (0:ℝ)..e, U (s + t) x) = ∫ u in (0 + t)..(e + t), U u x :=
      intervalIntegral.integral_comp_add_right (fun u => U u x) t
    have h6 : (∫ u in (t:ℝ)..(e + t), U u x) = F (e + t) - F t := by
      rw [hFdef]
      exact (intervalIntegral.integral_interval_sub_left
        (intervalIntegrable_apply hU x 0 (e + t)) (intervalIntegrable_apply hU x 0 t)).symm
    rw [h1, h2, h4, h5]
    simp only [zero_add]
    rw [h6]
  have hderiv : HasDerivAt (fun t : ℝ => (e⁻¹ : ℝ) • (F (e + t) - F t))
      ((e⁻¹ : ℝ) • (U e x - U 0 x)) 0 := by
    have hA : HasDerivAt (fun t : ℝ => F (e + t)) (U e x) 0 := by
      have hshift : HasDerivAt (fun t : ℝ => e + t) (1 : ℝ) 0 :=
        HasDerivAt.const_add e (hasDerivAt_id (0:ℝ))
      have h := HasDerivAt.scomp (0:ℝ) (hFderiv (e + 0)) hshift
      simpa [Function.comp] using h
    have hB : HasDerivAt (fun t : ℝ => F t) (U 0 x) 0 := hFderiv 0
    exact (hA.sub hB).const_smul (e⁻¹ : ℝ)
  have hfun : (fun t : ℝ => (e⁻¹ : ℝ) • (F (e + t) - F t))
      = fun t : ℝ => U t ((e⁻¹ : ℝ) • ∫ s in (0:ℝ)..e, U s x) := by
    funext t; rw [hkey t]
  rw [hfun] at hderiv
  refine mem_generator_domain (y := (-I) • ((e⁻¹ : ℝ) • (U e x - U 0 x))) ?_
  have : (I : ℂ) • ((-I : ℂ) • ((e⁻¹ : ℝ) • (U e x - U 0 x)))
      = (e⁻¹ : ℝ) • (U e x - U 0 x) := by
    rw [smul_smul]
    simp [Complex.I_mul_I]
  rw [this]
  exact hderiv

/-- Quantitative approximation by the averages. -/
