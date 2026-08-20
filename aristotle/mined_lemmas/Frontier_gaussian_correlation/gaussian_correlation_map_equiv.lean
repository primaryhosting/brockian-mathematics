import Mathlib

/-!
# Gaussian Correlation
Category: Frontier — Fields Medal Work
Target: Frontier.gaussian_correlation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

open MeasureTheory ProbabilityTheory Set

/-- A set is *symmetric convex* if it is convex and invariant under `x ↦ -x`. -/

theorem gaussian_correlation_map_equiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] (T : E ≃L[ℝ] F)
    (h : GaussianCorrelationProperty F) : GaussianCorrelationProperty E := by
  intro μ hμ hsym K L hK hL hKm hLm
  haveI := hμ
  have hTm : Measurable (T : E → F) := T.continuous.measurable
  have hTsm : Measurable (T.symm : F → E) := T.symm.continuous.measurable
  set ν : Measure F := μ.map T with hν
  have hνsym : ν.map (fun y ↦ -y) = ν := by
    rw [hν, Measure.map_map (by fun_prop) hTm]
    have he : ((fun y : F ↦ -y) ∘ (T : E → F)) = ((T : E → F) ∘ (fun x : E ↦ -x)) := by
      funext x; simp
    rw [he, ← Measure.map_map hTm (by fun_prop), hsym]
  have hsc : ∀ S : Set E, IsSymmConvex S → IsSymmConvex ((T.symm : F → E) ⁻¹' S) := by
    intro S hS
    refine ⟨hS.1.linear_preimage (T.symm : F →ₗ[ℝ] E), ?_⟩
    intro x hx
    have hneg : (T.symm : F → E) (-x) = -((T.symm : F → E) x) := by simp
    simp only [Set.mem_preimage, hneg]
    exact hS.2 _ hx
  have happ : ∀ S : Set E, MeasurableSet S → ν ((T.symm : F → E) ⁻¹' S) = μ S := by
    intro S hS
    rw [hν, Measure.map_apply hTm (hTsm hS)]
    congr 1
    ext x
    simp
  have key := h ν (by rw [hν]; infer_instance) hνsym _ _ (hsc K hK) (hsc L hL)
    (hTsm hKm) (hTsm hLm)
  rw [happ K hKm, happ L hLm, ← Set.preimage_inter, happ _ (hKm.inter hLm)] at key
  exact key

/-- The independent (product) case: for a product of probability measures, a cylinder over the
first factor and a cylinder over the second factor satisfy the correlation inequality, with
equality. -/
