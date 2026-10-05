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
# Free Laplacian Essentially Self Adjoint Via Plancherel
Category: Brockian (Open Discharge)
Target: Brockian.FreeLaplacianPlancherel.freeLaplacian_essentiallySelfAdjoint_via_plancherel
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above is a plain block comment because Lean requires `import` to precede any
-- module docstring; the same header is repeated as a module docstring below.)

import Mathlib

/-!
# Free Laplacian Essentially Self Adjoint Via Plancherel
Category: Brockian (Open Discharge)
Target: Brockian.FreeLaplacianPlancherel.freeLaplacian_essentiallySelfAdjoint_via_plancherel
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory SchwartzMap Laplacian LineDeriv FourierTransform Real LinearPMap
open scoped ComplexConjugate

namespace Brockian.FreeLaplacianPlancherel

/-- Euclidean space `ℝ^d`, the configuration space of the free particle. -/
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The Hilbert space `L²(ℝ^d, ℂ)`. -/
noncomputable abbrev Hs (d : ℕ) := Lp ℂ 2 (volume : Measure (Space d))

variable {d : ℕ}

/-- The symbol (Fourier multiplier) of `-Δ`, namely `4π²‖ξ‖²`. -/

lemma adjoint_isFormalAdjoint_self :
    ((freeLaplacianPMap d)†).IsFormalAdjoint ((freeLaplacianPMap d)†) := by
  intro u v
  have hu := fourier_adjoint_apply u
  have hv := fourier_adjoint_apply v
  have h1 : inner ℂ ((freeLaplacianPMap d)† u) (v : Hs d)
      = inner ℂ (𝓕 ((freeLaplacianPMap d)† u)) (𝓕 (v : Hs d)) :=
    (MeasureTheory.Lp.inner_fourier_eq _ _).symm
  have h2 : inner ℂ ((u : Hs d)) ((freeLaplacianPMap d)† v)
      = inner ℂ (𝓕 (u : Hs d)) (𝓕 ((freeLaplacianPMap d)† v)) :=
    (MeasureTheory.Lp.inner_fourier_eq _ _).symm
  rw [h1, h2, MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hu, hv] with ξ hξu hξv
  simp only [RCLike.inner_apply] at *
  rw [hξu, hξv]
  simp only [map_mul, Complex.conj_ofReal]
  ring

/-- **The free Laplacian is essentially self-adjoint.**

`freeLaplacianPMap d` is the operator `-Δ` on `L²(ℝ^d)` with domain the Schwartz space.
Essential self-adjointness of a densely defined symmetric operator `T` is exactly
self-adjointness of its adjoint `T†` (equivalently `T†† = T†`, i.e. the closure `T†† = T̄` of `T`
is self-adjoint).  The proof goes through the Plancherel theorem: on the Fourier side `-Δ` is
multiplication by the real symbol `4π²‖ξ‖²`. -/
