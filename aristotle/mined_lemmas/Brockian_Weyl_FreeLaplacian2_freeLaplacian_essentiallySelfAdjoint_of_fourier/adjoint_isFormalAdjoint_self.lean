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

lemma adjoint_isFormalAdjoint_self :
    (freeLaplacian V).adjoint.IsFormalAdjoint (freeLaplacian V).adjoint := by
  intro g₁ g₂
  have h1 : inner ℂ ((freeLaplacian V).adjoint g₁) (g₂ : L2Space V)
      = inner ℂ (𝓕 ((freeLaplacian V).adjoint g₁) : L2Space V)
        (𝓕 (g₂ : L2Space V) : L2Space V) := (MeasureTheory.Lp.inner_fourier_eq _ _).symm
  have h2 : inner ℂ (g₁ : L2Space V) ((freeLaplacian V).adjoint g₂)
      = inner ℂ (𝓕 (g₁ : L2Space V) : L2Space V)
        (𝓕 ((freeLaplacian V).adjoint g₂) : L2Space V) := (MeasureTheory.Lp.inner_fourier_eq _ _).symm
  rw [h1, h2, MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [fourier_adjoint_apply V g₁, fourier_adjoint_apply V g₂] with x hx1 hx2
  rw [RCLike.inner_apply, RCLike.inner_apply, hx1, hx2]
  simp [Complex.conj_ofReal]
  ring

/-- **The free Laplacian is essentially self-adjoint on the Schwartz space**, proved by
Fourier diagonalization: on the Fourier side `-Δ` becomes multiplication by `(2π)²‖ξ‖²`. -/
