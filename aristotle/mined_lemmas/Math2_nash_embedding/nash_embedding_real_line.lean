import Mathlib

/-!
# Nash Embedding
Category: Frontier Math
Target: Math2.nash_embedding
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Manifold ContDiff
open Bundle

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace Math2

/-!
## Isometric embeddings of Riemannian manifolds into Euclidean space

Throughout, a *Riemannian manifold* is a smooth manifold `M` modelled on `(E, H, I)` whose
tangent bundle carries a `RiemannianBundle` structure, i.e. each tangent space
`TangentSpace I x` is endowed with an inner product (varying smoothly with `x` when one also
assumes `IsContMDiffRiemannianBundle`).  This is the Mathlib formulation of a Riemannian metric.
-/

/-- A map `f : M → ℝ^N` is an **isometric embedding** of the Riemannian manifold `M` if it is
smooth, a topological embedding, and its differential preserves inner products, i.e. the pullback
along `f` of the Euclidean metric of `ℝ^N` is the Riemannian metric of `M`. -/

theorem nash_embedding_real_line (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a) (hpos : ∀ x, 0 < a x) :
    letI : RiemannianBundle (fun x : ℝ ↦ TangentSpace 𝓘(ℝ, ℝ) x) :=
      ⟨(lineMetric a ha hpos).toRiemannianMetric⟩
    ∃ f : ℝ → EuclideanSpace ℝ (Fin 1), IsIsometricEmbedding 𝓘(ℝ, ℝ) ℝ 1 f := by
  set s : ℝ → ℝ := fun t ↦ Real.sqrt (a t) with hs
  have hsdiff : ContDiff ℝ ∞ s := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (Real.contDiffAt_sqrt (x := a x) (hpos x).ne').comp x ha.contDiffAt
  have hscont : Continuous s := hsdiff.continuous
  set A : ℝ → ℝ := fun x ↦ ∫ t in (0 : ℝ)..x, s t with hA
  have hAderiv : ∀ x, HasDerivAt A (s x) x := fun x ↦
    intervalIntegral.integral_hasDerivAt_right (hscont.intervalIntegrable _ _)
      (hscont.stronglyMeasurableAtFilter _ _) hscont.continuousAt
  have hderivA : deriv A = s := funext fun x ↦ (hAderiv x).deriv
  have hAdiff : ContDiff ℝ ∞ A := by
    rw [contDiff_infty_iff_deriv]
    exact ⟨fun x ↦ (hAderiv x).differentiableAt, by rw [hderivA]; exact hsdiff⟩
  have hmono : StrictMono A := by
    apply strictMono_of_deriv_pos
    intro x
    rw [hderivA]
    exact Real.sqrt_pos.2 (hpos x)
  have hembA : Topology.IsEmbedding A :=
    hmono.isEmbedding_of_ordConnected ((isPreconnected_range hAdiff.continuous).ordConnected)
  refine ⟨iota ∘ A, ?_, isEmbedding_iota.comp hembA, ?_⟩
  · rw [contMDiff_iff_contDiff]
    exact iota.contDiff.comp hAdiff
  · intro x v w
    have hfd : HasFDerivAt (iota ∘ A) (iota.comp ((1 : ℝ →L[ℝ] ℝ).smulRight (s x))) x :=
      iota.hasFDerivAt.comp x (hAderiv x)
    have hmf : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) (iota ∘ A) x
        = iota.comp ((1 : ℝ →L[ℝ] ℝ).smulRight (s x)) := by
      rw [mfderiv_eq_fderiv]; exact hfd.fderiv
    rw [hmf]
    show inner ℝ (iota ((show ℝ from v) • s x)) (iota ((show ℝ from w) • s x)) = _
    rw [inner_iota]
    show (show ℝ from v) • s x * ((show ℝ from w) • s x)
      = a x * ((show ℝ from v) * (show ℝ from w))
    have hss : s x * s x = a x := Real.mul_self_sqrt (hpos x).le
    simp only [smul_eq_mul]
    rw [← hss]
    ring

end Line

end Math2

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

