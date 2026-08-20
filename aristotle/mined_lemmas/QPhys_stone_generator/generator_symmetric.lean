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


theorem generator_symmetric (x y : (generator U).domain) :
    ⟪generator U x, (y : H)⟫_ℂ = ⟪(x : H), generator U y⟫_ℂ := by
  have h1 := hasDerivAt_generator U x
  have h2 := hasDerivAt_generator U y
  have hprod := HasDerivAt.inner ℂ h1 h2
  have hconst : (fun t : ℝ => ⟪U t (x : H), U t (y : H)⟫_ℂ) = fun _ : ℝ => ⟪(x : H), (y : H)⟫_ℂ := by
    funext t; exact hU.inner_map_map t _ _
  rw [hconst] at hprod
  have hzero := hprod.unique (hasDerivAt_const (0:ℝ) ((⟪(x : H), (y : H)⟫_ℂ : ℂ)))
  rw [hU.apply_zero] at hzero
  simp only [ContinuousLinearMap.one_apply, inner_smul_right, inner_smul_left,
    Complex.conj_I] at hzero
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hcancel : I * ⟪(x : H), generator U y⟫_ℂ = I * ⟪generator U x, (y : H)⟫_ℂ := by
    linear_combination hzero
  exact (mul_left_cancel₀ hI hcancel).symm

/-- A symmetric operator is contained in its adjoint. -/
