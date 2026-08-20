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

theorem exists_isometry_on_range (f : E →ₗ[ℂ] F) (g : E →ₗ[ℂ] G)
    (h : ∀ x, ‖f x‖ = ‖g x‖) :
    ∃ L : (LinearMap.range f) →ₗᵢ[ℂ] G,
      ∀ x : E, L ⟨f x, LinearMap.mem_range_self f x⟩ = g x := by
  have hker : LinearMap.ker f ≤ LinearMap.ker g := by
    intro x hx
    have hx' : f x = 0 := hx
    have hnx := h x
    rw [hx'] at hnx
    simp at hnx
    simpa [LinearMap.mem_ker] using hnx.symm
  set q : (E ⧸ LinearMap.ker f) →ₗ[ℂ] G := (LinearMap.ker f).liftQ g hker with hq
  set e : (E ⧸ LinearMap.ker f) ≃ₗ[ℂ] (LinearMap.range f) := f.quotKerEquivRange with he
  set L₀ : (LinearMap.range f) →ₗ[ℂ] G := q ∘ₗ (e.symm : (LinearMap.range f) →ₗ[ℂ] _) with hL₀
  have key : ∀ x : E, L₀ ⟨f x, LinearMap.mem_range_self f x⟩ = g x := by
    intro x
    have hx : e (Submodule.Quotient.mk x) = ⟨f x, LinearMap.mem_range_self f x⟩ := by
      apply Subtype.ext
      rw [he]
      exact f.quotKerEquivRange_apply_mk x
    rw [hL₀]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, ← hx,
      LinearEquiv.symm_apply_apply, hq, Submodule.liftQ_apply]
  refine ⟨⟨L₀, ?_⟩, key⟩
  rintro ⟨s, x, rfl⟩
  rw [key x]
  simpa using (h x).symm

/-- A norm-preserving pair of maps yields a contraction `T : F →ₗ G` with `T (f x) = g x`. -/
