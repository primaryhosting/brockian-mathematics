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

lemma freeLaplacian_isFormalAdjoint_self :
    (freeLaplacian V).IsFormalAdjoint (freeLaplacian V) := by
  rintro ⟨-, f, rfl⟩ ⟨-, f', rfl⟩
  rw [freeLaplacian_apply, freeLaplacian_apply]
  have e1 : inner ℂ (toL2 V (-(Δ f))) (toL2 V f')
      = inner ℂ (toL2 V (𝓕 (-(Δ f)))) (toL2 V (𝓕 f')) := by
    rw [← fourier_toL2, ← fourier_toL2, MeasureTheory.Lp.inner_fourier_eq]
  have e2 : inner ℂ (toL2 V f) (toL2 V (-(Δ f')))
      = inner ℂ (toL2 V (𝓕 f)) (toL2 V (𝓕 (-(Δ f')))) := by
    rw [← fourier_toL2, ← fourier_toL2, MeasureTheory.Lp.inner_fourier_eq]
  rw [e1, e2, inner_toL2, inner_toL2]
  refine integral_congr_ae ?_
  filter_upwards [SchwartzMap.coeFn_toLp (𝓕 (-(Δ f)) : 𝓢(V, ℂ)) 2 (volume : Measure V),
    SchwartzMap.coeFn_toLp (𝓕 f : 𝓢(V, ℂ)) 2 (volume : Measure V)] with x hx1 hx2
  rw [show ((toL2 V (𝓕 (-(Δ f))) : L2Space V) : V → ℂ) x = 𝓕 (-(Δ f) : 𝓢(V, ℂ)) x from hx1,
    show ((toL2 V (𝓕 f) : L2Space V) : V → ℂ) x = 𝓕 f x from hx2,
    fourier_neg_laplacian_apply, fourier_neg_laplacian_apply]
  simp [Complex.conj_ofReal]
  ring

