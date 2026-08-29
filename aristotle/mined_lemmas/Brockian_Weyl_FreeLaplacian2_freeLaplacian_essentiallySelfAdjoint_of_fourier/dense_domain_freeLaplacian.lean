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

lemma dense_domain_freeLaplacian : Dense ((freeLaplacian V).domain : Set (L2Space V)) := by
  have h := SchwartzMap.denseRange_toLpCLM (E := V) (F := ℂ) (p := 2) ENNReal.ofNat_ne_top
    (μ := (volume : Measure V))
  have hset : ((freeLaplacian V).domain : Set (L2Space V))
      = Set.range (toLpCLM ℝ ℂ 2 volume) := rfl
  rw [hset]
  exact h

/-- Multiplication of a Schwartz function by the Fourier multiplier of `-Δ`, realized as a
Schwartz function via the Fourier transform. -/
