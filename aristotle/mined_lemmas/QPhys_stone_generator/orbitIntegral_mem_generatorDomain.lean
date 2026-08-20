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


theorem orbitIntegral_mem_generatorDomain [CompleteSpace H] {U : ℝ → H →L[ℂ] H} (hU : IsUnitaryGroup U) (x : H)
    (e : ℝ) : (∫ t in (0 : ℝ)..e, U t x) ∈ generatorDomain U := by
  have h1 : HasDerivAt (fun s : ℝ => ∫ t in (0 : ℝ)..(e + s), U t x) (U e x) 0 :=
    HasDerivAt.comp_const_add e 0 (by simpa using hasDerivAt_orbitIntegral hU x e)
  have h2 : HasDerivAt (fun s : ℝ => ∫ t in (0 : ℝ)..s, U t x) (U 0 x) 0 :=
    hasDerivAt_orbitIntegral hU x 0
  have h3 : HasDerivAt (fun s : ℝ => U s (∫ t in (0 : ℝ)..e, U t x)) (U e x - U 0 x) 0 := by
    simpa only [orbitIntegral_group hU x e] using h1.sub h2
  exact h3.differentiableAt

/-- The domain of the generator is dense. -/
