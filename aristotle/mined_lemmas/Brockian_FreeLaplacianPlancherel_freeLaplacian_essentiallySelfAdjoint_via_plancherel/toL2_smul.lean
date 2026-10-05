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

theorem toL2_smul {d : ℕ} (c : ℂ) (f : 𝓢(Eucl d, ℂ)) : toL2 (c • f) = c • toL2 f := by
  show (c • f).toLp 2 volume = c • (f.toLp 2 volume)
  rw [← SchwartzMap.toLpCLM_apply (𝕜 := ℂ) (f := c • f),
    ← SchwartzMap.toLpCLM_apply (𝕜 := ℂ) (f := f), map_smul]

