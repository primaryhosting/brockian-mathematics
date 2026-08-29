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

lemma ae_eq_multiplier_mul (G W : L2Space V)
    (h : ∀ φ : 𝓢(V, ℂ), inner ℂ W (toL2 V φ) = inner ℂ G (toL2 V (mulMultiplier V φ))) :
    (W : V → ℂ) =ᵐ[volume] fun ξ => (multiplier ξ : ℂ) * (G : V → ℂ) ξ := by
  refine ae_eq_of_integral_contDiff_smul_eq (locallyIntegrable_of_L2 V W)
    (locallyIntegrable_multiplier_mul V G) ?_
  intro g hg hgs
  have hcs : HasCompactSupport fun x => ((g x : ℝ) : ℂ) :=
    hgs.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  have hcd : ContDiff ℝ (⊤ : ℕ∞) fun x => ((g x : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp hg
  set φ : 𝓢(V, ℂ) := hcs.toSchwartzMap hcd with hφ
  have hφa : ∀ x, φ x = ((g x : ℝ) : ℂ) := fun x => rfl
  have h1 := h φ
  rw [inner_toL2, inner_toL2] at h1
  have h2 : ∫ ξ, (starRingEnd ℂ) ((W : V → ℂ) ξ) * ((g ξ : ℝ) : ℂ)
      = ∫ ξ, (starRingEnd ℂ) ((G : V → ℂ) ξ) * ((multiplier ξ : ℂ) * ((g ξ : ℝ) : ℂ)) := by
    simpa [hφa, mulMultiplier_apply] using h1
  have h3 := congrArg (starRingEnd ℂ) h2
  rw [← integral_conj, ← integral_conj] at h3
  simp only [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply,
    Complex.conj_ofReal] at h3
  calc ∫ x, g x • (W : V → ℂ) x
      = ∫ x, (W : V → ℂ) x * ((g x : ℝ) : ℂ) := by
        simp [Complex.real_smul, mul_comm]
    _ = ∫ x, (G : V → ℂ) x * ((multiplier x : ℂ) * ((g x : ℝ) : ℂ)) := h3
    _ = ∫ x, g x • ((multiplier x : ℂ) * (G : V → ℂ) x) := by
        simp [Complex.real_smul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

/-- The adjoint of the free Laplacian acts as multiplication by `(2π)²‖ξ‖²` on the Fourier
side. -/
