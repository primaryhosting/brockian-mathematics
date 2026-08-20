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


theorem generator_isFormalAdjoint {U : ℝ → H →L[ℂ] H} (hU : IsUnitaryGroup U) :
    (generator U).IsFormalAdjoint (generator U) := by
  intro x y
  have hf := hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_generator x)
  have hg := hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_generator_neg y)
  have t1 : Filter.Tendsto
      (fun h : ℝ => ⟪slope (fun t : ℝ => U t (x : H)) 0 h, (y : H)⟫_ℂ) (𝓝[≠] (0 : ℝ))
      (𝓝 ⟪Complex.I • generator U x, (y : H)⟫_ℂ) := hf.inner tendsto_const_nhds
  have t2 : Filter.Tendsto
      (fun h : ℝ => ⟪(x : H), slope (fun t : ℝ => U (-t) (y : H)) 0 h⟫_ℂ) (𝓝[≠] (0 : ℝ))
      (𝓝 ⟪(x : H), -(Complex.I • generator U y)⟫_ℂ) := tendsto_const_nhds.inner hg
  have hfun : (fun h : ℝ => ⟪slope (fun t : ℝ => U t (x : H)) 0 h, (y : H)⟫_ℂ)
      = fun h : ℝ => ⟪(x : H), slope (fun t : ℝ => U (-t) (y : H)) 0 h⟫_ℂ := by
    funext h
    have key : ⟪U h (x : H) - (x : H), (y : H)⟫_ℂ = ⟪(x : H), U (-h) (y : H) - (y : H)⟫_ℂ := by
      rw [inner_sub_left, inner_sub_right, hU.inner_apply_left]
    simp only [slope, vsub_eq_sub, sub_zero, hU.apply_zero, neg_zero]
    simp [key]
  rw [hfun] at t1
  have heq := tendsto_nhds_unique t1 t2
  have h2 : ⟪(generator U x : H), (y : H)⟫_ℂ * Complex.I
      = Complex.I * ⟪(x : H), (generator U y : H)⟫_ℂ := by
    simpa [inner_smul_left, inner_smul_right, Complex.conj_I] using heq
  refine mul_left_cancel₀ Complex.I_ne_zero ?_
  rw [← h2]
  ring

/-- If `y` admits a formal adjoint value `z`, i.e. `⟪z, u⟫ = ⟪y, A u⟫` for all `u` in the domain
of the generator, then `y` itself lies in the domain of the generator and `A y = z`.
This is the heart of Stone's theorem. -/
