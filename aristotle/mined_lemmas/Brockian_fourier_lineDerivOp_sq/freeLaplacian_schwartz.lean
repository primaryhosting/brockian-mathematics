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
# The Fourier transform of the Laplacian on Schwartz space

We record the classical formula `𝓕 (Δ f) ξ = -(4π²‖ξ‖²) 𝓕 f ξ` for Schwartz functions,
introduce the Fourier symbol `freeSymbol ξ = 4π²‖ξ‖²` of the free Laplacian `-Δ`, and show that
the "resolvent multiplier" `ξ ↦ (1 + freeSymbol ξ)⁻¹` has temperate growth (so that multiplying
a Schwartz function by it produces again a Schwartz function).
-/

namespace Brockian

open MeasureTheory SchwartzMap Real LineDeriv
open scoped FourierTransform SchwartzMap ComplexInnerProductSpace

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]


theorem freeLaplacian_schwartz (f : 𝓢(V, ℂ)) :
    ∃ hmem : (schwartzToL2 f : L2 V) ∈ (freeLaplacian (V := V)).domain,
      freeLaplacian ⟨schwartzToL2 f, hmem⟩ = schwartzToL2 (negLaplacianSchwartz f) := by
  obtain ⟨hmem, hval⟩ := mulOp_freeSymbol_schwartz (𝓕 f) (𝓕 (negLaplacianSchwartz f))
    (fun ξ => by rw [negLaplacianSchwartz_apply, fourier_neg_laplacian])
  have hdom : (schwartzToL2 f : L2 V) ∈ (freeLaplacian (V := V)).domain := by
    show fourierU V (schwartzToL2 f) ∈ (mulOp (freeSymbol : V → ℝ)).domain
    rw [fourierU_schwartzToL2]
    exact hmem
  refine ⟨hdom, ?_⟩
  have h1 : freeLaplacian ⟨schwartzToL2 f, hdom⟩
      = (fourierU V).symm (mulOp freeSymbol ⟨fourierU V (schwartzToL2 f), hdom⟩) := rfl
  rw [h1]
  have h2 : (⟨fourierU V (schwartzToL2 f), hdom⟩ : (mulOp (freeSymbol : V → ℝ)).domain)
      = ⟨schwartzToL2 (𝓕 f), hmem⟩ := Subtype.ext (fourierU_schwartzToL2 f)
  rw [h2, hval, fourierU_symm_schwartzToL2]
  congr 1
  exact FourierTransform.fourierInv_fourier_eq _

/-- The maximal free Laplacian extends `-Δ` on Schwartz functions. -/
