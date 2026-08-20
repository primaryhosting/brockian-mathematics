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


theorem isUnitaryGroup_phaseGroup : IsUnitaryGroup phaseGroup where
  map_zero := by
    ext
    simp [phaseGroup]
  map_add s t := by
    ext
    simp only [phaseGroup, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.coe_comp', Function.comp_apply, smul_eq_mul]
    rw [← mul_assoc, ← Complex.exp_add]
    push_cast
    ring_nf
  inner_map t x y := by
    have h : Complex.exp ((t : ℂ) * Complex.I) * Complex.exp (-((t : ℂ) * Complex.I)) = 1 := by
      rw [← Complex.exp_add]; simp
    simp only [phaseGroup, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      RCLike.inner_apply, smul_eq_mul, map_mul, ← Complex.exp_conj, Complex.conj_I,
      Complex.conj_ofReal, mul_neg]
    calc Complex.exp ((t : ℂ) * Complex.I) * y
            * (Complex.exp (-((t : ℂ) * Complex.I)) * (starRingEnd ℂ) x)
        = (Complex.exp ((t : ℂ) * Complex.I) * Complex.exp (-((t : ℂ) * Complex.I)))
            * (y * (starRingEnd ℂ) x) := by ring
      _ = y * (starRingEnd ℂ) x := by rw [h, one_mul]
  continuous_apply x := by
    unfold phaseGroup
    fun_prop

