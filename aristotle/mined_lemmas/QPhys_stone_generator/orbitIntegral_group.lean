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

set_option grind.warning false

/-!
# Stone's theorem: the generator of a strongly continuous one-parameter unitary group

We define the (skew-)generator of a strongly continuous one-parameter unitary group
`U : ℝ → H →L[ℂ] H` on a complex Hilbert space `H` as the unbounded operator
`A x = -i * (d/dt)|_{t=0} U t x`, with domain the set of vectors at which `t ↦ U t x`
is differentiable at `0`.

The main result `QPhys.stone_generator` states that this operator is densely defined and
self-adjoint, i.e. `(generator U)† = generator U`.
-/

namespace QPhys

open Filter Topology Complex
open scoped InnerProductSpace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A strongly continuous one-parameter unitary group on a complex Hilbert space. -/
structure IsUnitaryGroup (U : ℝ → H →L[ℂ] H) : Prop where
  /-- `U 0` is the identity. -/
  map_zero : U 0 = 1
  /-- `U` is a one-parameter group. -/
  map_add : ∀ s t : ℝ, U (s + t) = (U s).comp (U t)
  /-- Each `U t` preserves the inner product. -/
  inner_map : ∀ (t : ℝ) (x y : H), ⟪U t x, U t y⟫_ℂ = ⟪x, y⟫_ℂ
  /-- `U` is strongly continuous. -/
  continuous_apply : ∀ x : H, Continuous fun t => U t x

namespace IsUnitaryGroup

variable {U : ℝ → H →L[ℂ] H} (hU : IsUnitaryGroup U)
include hU


theorem orbitIntegral_group [CompleteSpace H] {U : ℝ → H →L[ℂ] H} (hU : IsUnitaryGroup U) (x : H) (e s : ℝ) :
    U s (∫ t in (0 : ℝ)..e, U t x)
      = (∫ t in (0 : ℝ)..(e + s), U t x) - ∫ t in (0 : ℝ)..s, U t x := by
  have h1 : U s (∫ t in (0 : ℝ)..e, U t x) = ∫ t in (0 : ℝ)..e, U s (U t x) :=
    ((U s).intervalIntegral_comp_comm (intervalIntegrable_orbit hU x 0 e)).symm
  have h2 : (fun t : ℝ => U s (U t x)) = fun t : ℝ => U (t + s) x := by
    funext t
    rw [← hU.apply_add, add_comm]
  have h3 : (∫ t in (0 : ℝ)..e, U (t + s) x) = ∫ t in (0 + s)..(e + s), U t x :=
    intervalIntegral.integral_comp_add_right (fun t : ℝ => U t x) s
  have h4 : (∫ t in (0 : ℝ)..(e + s), U t x) - (∫ t in (0 : ℝ)..s, U t x)
      = ∫ t in s..(e + s), U t x :=
    intervalIntegral.integral_interval_sub_left (intervalIntegrable_orbit hU x 0 (e + s))
      (intervalIntegrable_orbit hU x 0 s)
  rw [h1, h2, h3, h4, zero_add]

/-- Averages of an orbit over `[0, e]` belong to the domain of the generator. -/
