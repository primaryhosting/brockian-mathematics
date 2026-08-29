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

lemma projDiff_trace_sq {u v : n → ℂ} (hu : inn u u = 1) (hv : inn v v = 1) :
    ((rankOneProj u - rankOneProj v) * (rankOneProj u - rankOneProj v)).trace
      = ((2 * (1 - ‖inn u v‖ ^ 2) : ℝ) : ℂ) := by
  set P := rankOneProj u
  set Q := rankOneProj v
  have hPP : P * P = P := proj_mul_self hu
  have hQQ : Q * Q = Q := proj_mul_self hv
  have e : (P - Q) * (P - Q) = P*P - P*Q - Q*P + Q*Q := by noncomm_ring
  rw [e, hPP, hQQ]
  rw [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub, trace_rankOneProj,
    trace_rankOneProj, hu, hv, trace_proj_mul_proj, trace_proj_mul_proj, norm_inn_swap]
  push_cast
  ring

end RankOne

/-! ## Spectral input -/

section Spectral

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Eigenvalues of a Hermitian matrix satisfying `A³ = t • A` satisfy `λ³ = t λ`. -/
