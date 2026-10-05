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

theorem inner_toL2_eq_integral {d : ℕ} (a b : 𝓢(Eucl d, ℂ)) :
    inner ℂ (toL2 a) (toL2 b) = ∫ ξ, (starRingEnd ℂ) (𝓕 a ξ) * 𝓕 b ξ := by
  have h1 : inner ℂ (toL2 a) (toL2 b) = ∫ x, inner ℂ (a x) (b x) := by
    rw [toL2, toL2, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [a.coeFn_toLp 2 (volume : Measure (Eucl d)),
      b.coeFn_toLp 2 (volume : Measure (Eucl d))] with x hx1 hx2
    rw [hx1, hx2]
  rw [h1, ← SchwartzMap.integral_inner_fourier_fourier a b]
  simp [RCLike.inner_apply, mul_comm]

/-- The Schwartz core is dense in `L²(ℝ^d)`. -/
