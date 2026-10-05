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

theorem dense_range_shift (c : ℂ) (hc : ∀ ξ : V, ((symb ξ : ℝ) : ℂ) + c ≠ 0) :
    Dense (Set.range fun f : 𝓢(V, ℂ) => ((-Δ f) + c • f).toLp 2 volume) := by
  set Ψ : 𝓢(V, ℂ) →L[ℂ] Lp (α := V) ℂ 2 volume :=
    (SchwartzMap.toLpCLM ℂ ℂ 2 volume).comp
      (-(LineDeriv.laplacianCLM ℂ V 𝓢(V, ℂ)) + c • ContinuousLinearMap.id ℂ 𝓢(V, ℂ)) with hΨ
  have hΨapp : ∀ f, Ψ f = ((-Δ f) + c • f).toLp 2 volume := by
    intro f
    simp only [hΨ, ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.id_apply,
      SchwartzMap.laplacianCLM_eq, SchwartzMap.toLpCLM_apply]
  set K : Submodule ℂ (Lp (α := V) ℂ 2 volume) := LinearMap.range (Ψ : 𝓢(V, ℂ) →ₗ[ℂ] _) with hK
  have hrange : (Set.range fun f : 𝓢(V, ℂ) => ((-Δ f) + c • f).toLp 2 volume) = (K : Set _) := by
    ext v
    simp only [hK, SetLike.mem_coe, LinearMap.mem_range, Set.mem_range]
    constructor
    · rintro ⟨f, rfl⟩; exact ⟨f, hΨapp f⟩
    · rintro ⟨f, rfl⟩; exact ⟨f, (hΨapp f).symm⟩
  rw [hrange, Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro u hu
  refine eq_zero_of_orthogonal c hc u fun f => ?_
  have hmem : Ψ f ∈ K := LinearMap.mem_range_self _ f
  have := (Submodule.mem_orthogonal K u).mp hu (Ψ f) hmem
  rwa [hΨapp f] at this

/-! ### The free Laplacian as an operator with Schwartz domain -/

