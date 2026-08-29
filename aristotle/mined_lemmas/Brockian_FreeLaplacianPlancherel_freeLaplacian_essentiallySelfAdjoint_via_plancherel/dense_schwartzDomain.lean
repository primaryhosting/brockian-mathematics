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

import Mathlib

/-!
# Free Laplacian Essentially Self Adjoint Via Plancherel
Category: Brockian (Open Discharge)
Target: Brockian.FreeLaplacianPlancherel.freeLaplacian_essentiallySelfAdjoint_via_plancherel
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory SchwartzMap ComplexInnerProductSpace FourierTransform Laplacian Real

namespace Brockian.FreeLaplacianPlancherel

noncomputable section

/-! ## An abstract criterion for essential self-adjointness

We work with a symmetric, densely defined operator `T` with domain a submodule `D` of a complex
Hilbert space `H`.  Mathlib does not (yet) have a theory of unbounded operators, so we spell out
the relevant notions.
-/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `IsAdjointPair D T y z` says that `y` belongs to the domain of the adjoint of the operator
`T` (with domain `D`) and that `z` is a corresponding adjoint value, i.e.
`⟪T x, y⟫ = ⟪x, z⟫` for all `x` in the domain.  If `D` is dense then `z` is uniquely determined
by `y`, and `z = T* y`. -/

theorem dense_schwartzDomain : Dense (schwartzDomain (V := V) : Set (Lp (α := V) ℂ 2 volume)) := by
  have h := SchwartzMap.denseRange_toLpCLM (E := V) (F := ℂ) (p := 2) (μ := (volume : Measure V))
    (by simp)
  have hset : Set.range (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure V))
      = (schwartzDomain (V := V) : Set (Lp (α := V) ℂ 2 volume)) := by
    ext v
    simp only [Set.mem_range, SetLike.mem_coe, schwartzDomain, LinearMap.mem_range]
    constructor
    · rintro ⟨f, rfl⟩; exact ⟨f, rfl⟩
    · rintro ⟨f, rfl⟩; exact ⟨f, rfl⟩
  rw [← hset]
  exact h

/-- The free Laplacian is symmetric on its Schwartz domain. -/
