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
# Free Laplacian Essentially Self Adjoint Via Plancherel
Category: Brockian (Open Discharge)
Target: Brockian.FreeLaplacianPlancherel.freeLaplacian_essentiallySelfAdjoint_via_plancherel
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian.FreeLaplacianPlancherel

open MeasureTheory SchwartzMap FourierTransform Laplacian LineDeriv

/-- Euclidean space `ℝ^d`, the configuration space of the free Laplacian. -/
abbrev Eucl (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The Hilbert space `L²(ℝ^d, ℂ)`. -/
noncomputable abbrev L2 (d : ℕ) := Lp (α := Eucl d) ℂ 2 volume

/-- A Schwartz function, viewed as an element of `L²(ℝ^d)`. The Schwartz space is the core
(dense domain) on which we consider the free Laplacian. -/

theorem integral_conj_mul_symbol_eq_zero {d : ℕ} (z : ℂ) (u : L2 d)
    (horth : ∀ f : 𝓢(Eucl d, ℂ), inner ℂ (freeLaplacian f + z • toL2 f) u = 0)
    (g : 𝓢(Eucl d, ℂ)) :
    ∫ ξ, (starRingEnd ℂ) (g ξ) *
      (((symbol ξ : ℂ) + (starRingEnd ℂ) z) * ((𝓕 u : L2 d) : Eucl d → ℂ) ξ) = 0 := by
  set f : 𝓢(Eucl d, ℂ) := 𝓕⁻ g with hfdef
  have hFf : 𝓕 f = g := fourier_fourierInv_eq g
  have h1 : inner ℂ (𝓕 (freeLaplacian f + z • toL2 f)) (𝓕 u) = 0 := by
    rw [Lp.inner_fourier_eq]; exact horth f
  have h2 : 𝓕 (freeLaplacian f + z • toL2 f) = toL2 (𝓕 (-(Δ f)) + z • g) := by
    rw [toL2_add, toL2_smul, FourierAdd.fourier_add, FourierSMul.fourier_smul]
    congr 1
    · rw [freeLaplacian, toL2, toL2, SchwartzMap.toLp_fourier_eq]
    · rw [toL2, toL2, SchwartzMap.toLp_fourier_eq, hFf]
  rw [h2, L2.inner_def] at h1
  rw [← h1]
  simp only [toL2]
  apply integral_congr_ae
  filter_upwards [(𝓕 (-(Δ f)) + z • g).coeFn_toLp 2 (volume : Measure (Eucl d))] with ξ hξ
  rw [hξ]
  simp only [SchwartzMap.add_apply, SchwartzMap.smul_apply, RCLike.inner_apply,
    fourier_freeLaplacian_apply, hFf, map_add, map_mul, Complex.conj_ofReal, smul_eq_mul]
  ring

/-- The deficiency criterion: for non-real `z`, the range of `-Δ + z` on the Schwartz core is
dense in `L²(ℝ^d)`. -/
