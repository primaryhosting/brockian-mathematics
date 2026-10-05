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

def multiplier {W : Type*} [NormedAddCommGroup W] (ξ : W) : ℝ := (2 * π) ^ 2 * ‖ξ‖ ^ 2

lemma fourier_laplacian_apply (f : 𝓢(V, ℂ)) (ξ : V) :
    𝓕 (Δ f : 𝓢(V, ℂ)) ξ = (-(multiplier ξ) : ℝ) * 𝓕 f ξ := by
  classical
  set b := stdOrthonormalBasis ℝ V with hb
  have hstep : ∀ (g : 𝓢(V, ℂ)) (m : V) (x : V),
      𝓕 (∂_{m} g) x = (2 * π * Complex.I * (inner ℝ x m)) * 𝓕 g x := by
    intro g m x
    rw [SchwartzMap.fourier_lineDerivOp_eq]
    have hm : (fun y : V => (inner ℝ y m : ℝ)).HasTemperateGrowth := by fun_prop
    simp [hm]
    ring
  rw [SchwartzMap.laplacian_eq_sum b]
  have hsum : 𝓕 (∑ i, ∂_{b i} (∂_{b i} f) : 𝓢(V, ℂ))
      = ∑ i, 𝓕 (∂_{b i} (∂_{b i} f) : 𝓢(V, ℂ)) := by
    change (fourierTransformCLM ℂ) _ = _
    rw [map_sum]
    rfl
  rw [hsum, SchwartzMap.sum_apply]
  have key : ∀ i, 𝓕 (∂_{b i} (∂_{b i} f) : 𝓢(V, ℂ)) ξ
      = (-((2 * π) ^ 2 * (inner ℝ ξ (b i) : ℝ) ^ 2 : ℝ) : ℂ) * 𝓕 f ξ := by
    intro i
    rw [hstep, hstep]
    push_cast
    ring_nf
    simp [Complex.I_sq]
  have hnorm : ∑ i, (inner ℝ ξ (b i) : ℝ) ^ 2 = ‖ξ‖ ^ 2 := b.sum_sq_inner_left ξ
  simp_rw [key]
  rw [← Finset.sum_mul]
  congr 1
  simp only [multiplier]
  push_cast
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
  norm_cast
  rw [hnorm]

/-- The Fourier transform diagonalizes the free Laplacian: the Fourier transform of `-Δ f`
is the pointwise product of the multiplier `(2π)²‖ξ‖²` with the Fourier transform of `f`. -/
