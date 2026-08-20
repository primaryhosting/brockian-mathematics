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


theorem fourier_laplacian (f : 𝓢(V, ℂ)) (ξ : V) :
    𝓕 (laplacianCLM ℂ V 𝓢(V, ℂ) f) ξ = -(4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ) * 𝓕 f ξ := by
  classical
  set b := stdOrthonormalBasis ℝ V with hb
  rw [laplacianCLM_eq, SchwartzMap.laplacian_eq_sum b, ← fourierTransformCLM_apply (𝕜 := ℂ),
    map_sum]
  simp only [SchwartzMap.sum_apply, fourierTransformCLM_apply]
  rw [Finset.sum_congr rfl (fun i _ => fourier_lineDerivOp_sq f (b i) ξ)]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  have key : ∑ i, ((inner ℝ ξ (b i) : ℝ) : ℂ) ^ 2 = ((‖ξ‖ ^ 2 : ℝ) : ℂ) := by
    rw [← OrthonormalBasis.sum_sq_inner_left b ξ]
    push_cast
    ring
  rw [key]
  push_cast
  ring_nf
  simp [Complex.I_sq]

/-- The Fourier symbol of the free Laplacian `-Δ`. -/
