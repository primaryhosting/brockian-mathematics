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


theorem norm_sub_I_smul_sq (x : (generator U).domain) :
    ‖generator U x - I • (x : H)‖ ^ 2 = ‖generator U x‖ ^ 2 + ‖(x : H)‖ ^ 2 := by
  have hreal : ⟪generator U x, (x : H)⟫_ℂ = (starRingEnd ℂ) (⟪generator U x, (x : H)⟫_ℂ) := by
    rw [inner_conj_symm]
    exact generator_symmetric hU x x
  have him : (⟪generator U x, (x : H)⟫_ℂ).im = 0 := by
    have := congrArg Complex.im hreal
    simp only [Complex.conj_im] at this
    linarith
  have hnorm : ‖(I : ℂ) • (x : H)‖ = ‖(x : H)‖ := by
    rw [norm_smul]; simp
  have hre : RCLike.re (⟪generator U x, (I : ℂ) • (x : H)⟫_ℂ) = 0 := by
    rw [inner_smul_right]
    simp [RCLike.re_to_complex, him]
  rw [@norm_sub_sq ℂ, hnorm, hre]
  ring

