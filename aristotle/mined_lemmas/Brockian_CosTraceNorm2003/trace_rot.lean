/-
# Cos Trace Norm 2003
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2003
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian

/-- The squared Frobenius (Hilbert–Schmidt) norm of a square real matrix:
the sum of the squares of all its entries. -/

lemma trace_rot (θ : ℝ) : (rot θ).trace = 2 * Real.cos θ := by
  rw [rot, Matrix.trace_fin_two_of]; ring

/--
**Cos Trace Norm 2003.**

For every angle `θ`, the plane rotation `rot θ` has trace `2 cos θ`, and this trace
obeys the Cauchy–Schwarz trace-norm bound `|tr A| ≤ √n · ‖A‖_F` (here `n = 2`),
whose right-hand side equals `2`; consequently `|2 cos θ| ≤ 2`, with equality
exactly when `θ` is an integer multiple of `π`.
-/
