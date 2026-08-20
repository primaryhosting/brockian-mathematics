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
# The basic criterion for essential self-adjointness

This file develops the abstract operator-theoretic input for `Brockian.Weyl.FreeLaplacian2`:
a densely defined symmetric operator on a complex Hilbert space whose two deficiency ranges
`Ran (T + i)` and `Ran (T - i)` are dense has self-adjoint closure, i.e. it is
*essentially self-adjoint*.
-/

namespace Brockian.Weyl

open LinearPMap Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The operator `x ↦ T x + z • x` on the domain of `T`. -/

theorem dense_defRange (z : ℂ) (hz : z.im ≠ 0) :
    Dense (Brockian.Weyl.defRange (freeLaplacian V) z : Set (L2Space V)) := by
  set S : Set (L2Space V) := {x | ∃ ψ : 𝓢(V, ℂ), HasCompactSupport ψ ∧ toL2 V ψ = x}
  set e : L2Space V ≃ₜ L2Space V := (MeasureTheory.Lp.fourierTransformₗᵢ V ℂ).symm.toHomeomorph
  have hSdense : Dense S := dense_compactSupport_toL2 V
  have himage : Dense (e '' S) := by
    intro y
    rw [(e.image_closure S).symm, hSdense.closure_eq, Set.image_univ, e.surjective.range_eq]
    trivial
  refine Dense.mono ?_ himage
  rintro y ⟨x, ⟨ψ, hψ, rfl⟩, rfl⟩
  obtain ⟨u, hu⟩ := exists_schwartz_solution hz ψ hψ
  refine ⟨⟨toL2 V u, mem_freeLaplacian_domain V u⟩, ?_⟩
  have hfi : e (toL2 V ψ) = toL2 V (𝓕⁻ ψ) := by
    show 𝓕⁻ (ψ.toLp 2 volume) = _
    rw [SchwartzMap.toLp_fourierInv_eq]
    rfl
  rw [Brockian.Weyl.defOp_apply, freeLaplacian_apply, hfi, ← hu]
  simp [map_add, map_smul]

/-! ### The main theorem -/

/-- **The free Laplacian is essentially self-adjoint.**  The operator `-Δ` with domain the
Schwartz space, viewed as an unbounded operator on `L²(V, ℂ)`, is symmetric, densely defined,
and its closure is self-adjoint.  The proof goes through the Fourier transform: it turns `-Δ`
into multiplication by `4π²‖ξ‖²`, so that `(-Δ ± i)` can be inverted on a dense set of data. -/
