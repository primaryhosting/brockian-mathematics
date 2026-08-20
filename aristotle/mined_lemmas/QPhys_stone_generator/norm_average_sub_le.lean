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


theorem norm_average_sub_le (x : H) {e d : ℝ} (he : 0 < e)
    (hd : ∀ s ∈ Set.uIoc (0:ℝ) e, ‖U s x - x‖ ≤ d) :
    ‖((e⁻¹ : ℝ) • ∫ s in (0:ℝ)..e, U s x) - x‖ ≤ d := by
  have hconst : (∫ _s in (0:ℝ)..e, x) = e • x := by
    simp
  have hx : x = (e⁻¹ : ℝ) • (∫ _s in (0:ℝ)..e, x) := by
    rw [hconst, smul_smul, inv_mul_cancel₀ (ne_of_gt he), one_smul]
  have hsub : ((e⁻¹ : ℝ) • ∫ s in (0:ℝ)..e, U s x) - x
      = (e⁻¹ : ℝ) • ∫ s in (0:ℝ)..e, (U s x - x) := by
    rw [intervalIntegral.integral_sub (intervalIntegrable_apply hU x 0 e)
      (intervalIntegrable_const)]
    rw [smul_sub, ← hx]
  rw [hsub, norm_smul]
  have hbound : ‖∫ s in (0:ℝ)..e, (U s x - x)‖ ≤ d * |e| := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := e) (C := d)
      (f := fun s : ℝ => U s x - x) hd
    simpa using this
  have hnorm : ‖(e⁻¹ : ℝ)‖ = e⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hnorm]
  have habs : |e| = e := abs_of_pos he
  calc e⁻¹ * ‖∫ s in (0:ℝ)..e, (U s x - x)‖ ≤ e⁻¹ * (d * |e|) := by
        exact mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = d := by rw [habs]; field_simp

/-- The domain of the generator is dense. -/
