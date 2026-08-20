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
/-!
# Free Laplacian Essentially Self Adjoint Via Plancherel
Category: Brockian (Open Discharge)
Target: Brockian.FreeLaplacianPlancherel.freeLaplacian_essentiallySelfAdjoint_via_plancherel
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

open MeasureTheory SchwartzMap FourierTransform Complex
open scoped ComplexInnerProductSpace

namespace Brockian.FreeLaplacianPlancherel

/-! ## Abstract theory of graphs of unbounded operators -/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The graph of the adjoint of the (not necessarily bounded) operator whose graph is `G`:
the set of pairs `(g, h)` with `⟪T f, g⟫ = ⟪f, h⟫` for all `(f, T f) ∈ G`. -/

lemma fourier_freeLaplacian (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (𝓕 (freeLaplacian g) : 𝓢(ℝ, ℂ)) x = ((laplacianSymbol x : ℝ) : ℂ) * (𝓕 g : 𝓢(ℝ, ℂ)) x := by
  have hneg : (𝓕 (freeLaplacian g) : 𝓢(ℝ, ℂ))
      = -(𝓕 (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ g)) : 𝓢(ℝ, ℂ)) := by
    have hg : freeLaplacian g = -(SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ g)) := rfl
    rw [hg, ← SchwartzMap.fourierTransformCLM_apply ℂ, map_neg,
      SchwartzMap.fourierTransformCLM_apply]
  rw [hneg]
  have e1 := fourier_derivCLM (SchwartzMap.derivCLM ℂ ℂ g) x
  have e2 := fourier_derivCLM g x
  simp only [SchwartzMap.neg_apply, laplacianSymbol]
  rw [← e1, ← e2]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-! ### `L²` bookkeeping -/

