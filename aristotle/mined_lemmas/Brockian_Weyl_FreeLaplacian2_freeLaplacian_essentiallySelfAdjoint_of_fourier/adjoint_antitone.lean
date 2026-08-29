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

/-
# Free Laplacian Essentially Self Adjoint Of Fourier
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Free Laplacian Essentially Self Adjoint Of Fourier
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.Weyl.FreeLaplacian2

open MeasureTheory SchwartzMap Real LineDeriv
open scoped FourierTransform InnerProductSpace Laplacian

noncomputable section

/-- A densely defined operator `A` on a Hilbert space is *essentially self-adjoint* if its
adjoint is self-adjoint (equivalently, if the closure `A** = A*` of `A` is self-adjoint). -/

lemma adjoint_antitone {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] {T S : E →ₗ.[𝕜] E}
    (hT : Dense (T.domain : Set E)) (hS : Dense (S.domain : Set E)) (h : S ≤ T) :
    T.adjoint ≤ S.adjoint := by
  have hmem : ∀ y : T.adjoint.domain, (y : E) ∈ S.adjoint.domain := by
    intro y
    refine LinearPMap.mem_adjoint_domain_of_exists _ ⟨T.adjoint y, fun x => ?_⟩
    have hx : (x : E) ∈ T.domain := h.1 x.2
    have hSx : S x = T ⟨(x : E), hx⟩ := h.2 rfl
    rw [hSx]
    exact LinearPMap.adjoint_isFormalAdjoint hT y ⟨(x : E), hx⟩
  refine ⟨fun x hx => hmem ⟨x, hx⟩, ?_⟩
  rintro ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩ hyy
  subst hyy
  refine (LinearPMap.adjoint_apply_eq hS ⟨y₁, hy₂⟩ (x₀ := T.adjoint ⟨y₁, hy₁⟩) ?_).symm
  intro x
  have hx : (x : E) ∈ T.domain := h.1 x.2
  have hSx : S x = T ⟨(x : E), hx⟩ := h.2 rfl
  rw [hSx]
  exact LinearPMap.adjoint_isFormalAdjoint hT ⟨y₁, hy₁⟩ ⟨(x : E), hx⟩

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The Hilbert space `L²(V, ℂ)`. -/
abbrev L2Space := Lp (α := V) ℂ 2 volume

/-- The inclusion of Schwartz functions into `L²`. -/
