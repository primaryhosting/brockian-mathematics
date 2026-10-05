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
# Cos Trace Norm 2003
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2003
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires the `import` line to precede any module doc comment, so the
-- header block above appears immediately after the single required import.)

open scoped BigOperators
open scoped Real

namespace Brockian

open Matrix

/-! ## The trace norm of a Hermitian matrix -/

section Defs

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace norm (Schatten 1-norm) of a Hermitian matrix: the sum of the absolute
values of its eigenvalues. -/

theorem hermTraceNorm_projDiff {u v : n → ℂ} (hu : inn u u = 1) (hv : inn v v = 1) :
    hermTraceNorm (projDiff_isHermitian u v) = 2 * Real.sqrt (1 - ‖inn u v‖ ^ 2) := by
  set s := Real.sqrt (1 - ‖inn u v‖ ^ 2) with hsdef
  have hs2 : s ^ 2 = 1 - ‖inn u v‖ ^ 2 :=
    Real.sq_sqrt (one_sub_normSq_inn_nonneg hu hv)
  refine hermTraceNorm_of_cube _ (Real.sqrt_nonneg _) ?_ ?_
  · rw [hs2]; exact projDiff_cube hu hv
  · rw [hs2]; exact projDiff_trace_sq hu hv

/-- **Cos Trace Norm 2003.**  If `u` and `v` are unit vectors in `ℂⁿ` and `θ ∈ [0, π/2]` is the
angle between the lines they span, i.e. `cos θ = ‖⟪u, v⟫‖`, then the trace norm of the
difference of the corresponding rank-one projections equals `2 sin θ`. -/
