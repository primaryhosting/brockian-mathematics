import Mathlib

/-!
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Statement: Fidelity equals the maximal overlap over purifications (Uhlmann's theorem).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

namespace QI

open Matrix
open scoped ComplexOrder MatrixOrder

/-! ### Isometries defined on the range of a linear map -/

section Isom

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-- If `f` and `g` have the same norm pointwise, there is a linear isometry defined on the
range of `f` sending `f x` to `g x`. -/

theorem exists_contraction_extension [FiniteDimensional ℂ F] (f : E →ₗ[ℂ] F) (g : E →ₗ[ℂ] G)
    (h : ∀ x, ‖f x‖ = ‖g x‖) :
    ∃ T : F →ₗ[ℂ] G, (∀ x, T (f x) = g x) ∧ ∀ y, ‖T y‖ ≤ ‖y‖ := by
  obtain ⟨L, hL⟩ := exists_isometry_on_range f g h
  refine ⟨L.toLinearMap ∘ₗ ((LinearMap.range f).orthogonalProjection : F →ₗ[ℂ] _), ?_, ?_⟩
  · intro x
    have hx : (LinearMap.range f).orthogonalProjection (f x)
        = ⟨f x, LinearMap.mem_range_self f x⟩ := by
      apply Subtype.ext
      simpa using Submodule.starProjection_eq_self_iff.2 (LinearMap.mem_range_self f x)
    simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe,
      LinearIsometry.coe_toLinearMap, hx, hL x]
  · intro y
    simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe,
      LinearIsometry.coe_toLinearMap, LinearIsometry.norm_map]
    exact Submodule.norm_orthogonalProjection_apply_le _ y

/-- A norm-preserving pair of endomorphisms of a finite dimensional space is intertwined by a
global linear isometry. -/
