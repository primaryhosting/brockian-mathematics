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


noncomputable def generator (U : ℝ → H →L[ℂ] H) : H →ₗ.[ℂ] H where
  domain := generatorDomain U
  toFun :=
    { toFun := fun x => (-Complex.I) • deriv (fun t : ℝ => U t (x : H)) 0
      map_add' := by
        intro x y
        have hx : DifferentiableAt ℝ (fun t : ℝ => U t (x : H)) 0 := x.2
        have hy : DifferentiableAt ℝ (fun t : ℝ => U t (y : H)) 0 := y.2
        have hF : HasDerivAt (fun t : ℝ => U t ((x : H) + (y : H)))
            (deriv (fun t : ℝ => U t (x : H)) 0 + deriv (fun t : ℝ => U t (y : H)) 0) 0 := by
          simpa only [map_add] using hx.hasDerivAt.add hy.hasDerivAt
        rw [Submodule.coe_add, hF.deriv, smul_add]
      map_smul' := by
        intro c x
        have hx : DifferentiableAt ℝ (fun t : ℝ => U t (x : H)) 0 := x.2
        have hF : HasDerivAt (fun t : ℝ => U t (c • (x : H)))
            (c • deriv (fun t : ℝ => U t (x : H)) 0) 0 := by
          simpa only [map_smul] using hx.hasDerivAt.const_smul c
        rw [RingHom.id_apply, Submodule.coe_smul_of_tower, hF.deriv, smul_comm] }

